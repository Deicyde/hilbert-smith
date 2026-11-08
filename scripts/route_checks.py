#!/usr/bin/env python3
"""Route-separation checks of PLAN section 5 that need no Lean build.

1. Import boundary: no file of the library `HilbertSmith` imports a module of HS_proof, of
   `HSGeneral` or of `HSBridge` (the only libraries of this repository that may import HS_proof).
   Every file of the library is checked, so this is the whole import closure inside `src/`.
2. Coverage: every `src/HilbertSmith/**/*.lean` is imported, transitively, by
   `src/HilbertSmith.lean`, so the in-build check `#assert_import_boundary HilbertSmith` sees it.
3. The reference: `hsformal` comes from https://github.com/adbrw/HS_proof, at the same revision in
   `lakefile.toml` and `lake-manifest.json`; HS_proof's libraries at that revision are exactly the
   module roots this script and `src/HSBridge/Purity.lean` (`hsProofRoots`) count as HS_proof.
4. Pin equality: the `mathlib` and `TauCeti` revisions in `lake-manifest.json` equal those in
   HS_proof's `lake-manifest.json` at the pinned revision.
5. No copying: no tracked file declares the namespace of HS_proof's library, and no `.lean` file
   declares a name in it. No tracked `.lean` file, top-level declaration or docstring equals one
   of HS_proof's at the pinned revision, compared by digest after normalization (comments and
   whitespace removed for files and declarations; whitespace collapsed for docstrings).

HS_proof is read with git at the pinned revision: from `.lake/packages/hsformal` if that checkout
has the commit (a local build), otherwise fetched from GitHub into a temporary directory.

Run from the repository root: `python3 scripts/route_checks.py`. It first runs its self-tests
(import parsing and normalization). Exits 1 if a check fails.
"""

import hashlib
import json
import re
import subprocess
import sys
import tempfile
import tomllib
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
# The module roots of HS_proof's package `hsformal`, one per library (checked in `check_reference`).
HS_PROOF_ROOTS = ("HSFormal", "Challenge", "Solution", "FCChallenge", "FCSolution")
# Libraries of this repository that may import HS_proof, and so may not be imported by HilbertSmith.
BRIDGE_ROOTS = ("HSGeneral", "HSBridge")
HS_PROOF_URL = "https://github.com/adbrw/HS_proof"
PINNED = ("mathlib", "TauCeti")
# Written so that this file does not match its own checks.
NAMESPACE_RE = re.compile(r"\bnamespace\s+(?:_root_\.)?" + "HSFormal" + r"\b")
DECL_KEYWORDS = ("theorem", "lemma", "def", "abbrev", "instance", "structure", "class",
                 "inductive", "axiom", "opaque", "example")
DECL_IN_NAMESPACE_RE = re.compile(
    r"\b(?:" + "|".join(DECL_KEYWORDS) + r")\s+(?:_root_\.)?" + "HSFormal" + r"\.")
# Top-level units shorter than this (normalized) are not compared: they are too generic.
MIN_DECL_CHARS = 80
MIN_DOC_CHARS = 60

failures = []


def fail(msg):
    failures.append(msg)
    print(f"FAIL: {msg}")


def ok(msg):
    print(f"ok: {msg}")


def git(*args, cwd=ROOT, binary=False):
    out = subprocess.run(["git", *args], cwd=cwd, check=True, capture_output=True)
    return out.stdout if binary else out.stdout.decode()


# ### Lexing Lean text

IDENT_CHARS = re.compile(r"[\w'!?₀-₉ₐ-ₜᵢ-ᵪ]")


def lex(text):
    """Splits Lean text into code (comments replaced by a space) and the docstrings it contains.

    Handles nested block comments, `--` line comments, string literals with escapes, raw strings
    `r"…"`, `r#"…"#`, and character literals such as `'"'` and `'\\''`. A prime inside an
    identifier (`h'`) is not a character literal.
    """
    out, docs = [], []
    i, n = 0, len(text)
    while i < n:
        c, two = text[i], text[i:i + 2]
        prev = text[i - 1] if i else " "
        if two == "/-":
            doc = text[i + 2:i + 3] in ("-", "!") and text[i + 2:i + 4] != "-/"
            depth, j = 1, i + 2
            while j < n and depth:
                if text[j:j + 2] == "/-":
                    depth, j = depth + 1, j + 2
                elif text[j:j + 2] == "-/":
                    depth, j = depth - 1, j + 2
                else:
                    j += 1
            if doc:
                docs.append(text[i + 3:j - 2])
            out.append(" ")
            i = j
        elif two == "--":
            j = text.find("\n", i)
            i = n if j < 0 else j
        elif c == "r" and not IDENT_CHARS.match(prev) and re.match(r'r#*"', text[i:]):
            hashes = re.match(r'r(#*)"', text[i:]).group(1)
            end = text.find('"' + hashes, i + len(hashes) + 2)
            j = n if end < 0 else end + 1 + len(hashes)
            out.append(text[i:j])
            i = j
        elif c == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            out.append(text[i:j + 1])
            i = j + 1
        elif c == "'" and not IDENT_CHARS.match(prev):
            m = re.match(r"'(?:\\(?:x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4}|.)|[^\\'\n])'", text[i:])
            if m:
                out.append(m.group(0))
                i += len(m.group(0))
            else:
                out.append(c)
                i += 1
        else:
            out.append(c)
            i += 1
    return "".join(out), docs


def strip_ws(text):
    return re.sub(r"\s+", "", text)


def digest(text):
    return hashlib.sha256(text.encode()).hexdigest()


# ### Imports

HEADER_ITEM = re.compile(
    r"\s*(?:module\b|prelude\b|(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?(\S+))")


def imports_in(text):
    """The modules imported by the header of a Lean file, `«»` dropped."""
    code, _ = lex(text)
    mods, pos = [], 0
    while True:
        m = HEADER_ITEM.match(code, pos)
        if not m or m.end() == pos:
            break
        if m.group(1):
            mods.append(m.group(1).replace("«", "").replace("»", ""))
        pos = m.end()
    return mods


def imports_of(path):
    return imports_in(path.read_text(encoding="utf-8"))


# ### Declarations

COMMAND_START = re.compile(
    r"^(?:@\[|#|end\b|namespace\b|section\b|open\b|variable\b|universe\b|set_option\b|"
    r"attribute\b|noncomputable\b|private\b|protected\b|public\b|meta\b|partial\b|unsafe\b|"
    r"nonrec\b|mutual\b|export\b|local\b|scoped\b|macro\b|syntax\b|elab\b|notation\b|infix|"
    r"prefix\b|postfix\b|initialize\b|deriving\b|"
    + "|".join(k + r"\b" for k in DECL_KEYWORDS) + ")")
DECL_START = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*(?:(?:noncomputable|private|protected|public|meta|partial|unsafe|"
    r"nonrec)\s+)*(?:" + "|".join(DECL_KEYWORDS) + r")\b")


def declarations(text):
    """The top-level declarations of a Lean file, comments removed, whitespace removed.

    A command starts at a line in column 0 that begins with a command keyword; a declaration is a
    command whose keyword (after attributes and modifiers) is a declaration keyword.
    """
    code, _ = lex(text)
    units, current = [], None
    for line in code.splitlines():
        if line[:1].strip() and COMMAND_START.match(line):
            if current is not None:
                units.append(current)
            current = [line] if DECL_START.match(line) else None
        elif current is not None:
            current.append(line)
    if current is not None:
        units.append(current)
    return [u for u in (strip_ws("\n".join(u)) for u in units) if len(u) >= MIN_DECL_CHARS]


def docstrings(text):
    _, docs = lex(text)
    return [d for d in (re.sub(r"\s+", " ", d).strip() for d in docs) if len(d) >= MIN_DOC_CHARS]


# ### Self-tests

def self_test():
    cases = [
        ("meta import A.B\n", ["A.B"]),
        ("public meta import B\n", ["B"]),
        ("import C import D\n", ["C", "D"]),
        ("import\n  E\n", ["E"]),
        ("import «F».G\n", ["F.G"]),
        ("module\n/- c -/ public import H -- c\nimport all I\ndef x := 1\nimport J\n", ["H", "I"]),
    ]
    for text, expected in cases:
        got = imports_in(text)
        if got != expected:
            fail(f"self-test: imports of {text!r}: expected {expected}, got {got}")
    norm = [
        ("def s := \"a -- b\" -- c\n/- x -/ y", 'defs:="a--b"y'),
        ("def c := '\"' -- c\ndef d := 1", "defc:='\"'defd:=1"),
        ("def c := '\\'' /- c -/", "defc:='\\''"),
        ("def r := r#\"a \" -- b\"# -- c", 'defr:=r#"a"--b"#'),
        ("theorem h' : x' = 1 -- c", "theoremh':x'=1"),
        ("/-- doc -/ def a := 1 /- /- nested -/ -/", "defa:=1"),
    ]
    for text, expected in norm:
        got = strip_ws(lex(text)[0])
        if got != expected:
            fail(f"self-test: normalization of {text!r}: expected {expected!r}, got {got!r}")
    decl_text = ("namespace N\n\n/-- A docstring that is long enough to be compared by its "
                 "digest. -/\n@[simp] theorem t (n : Nat) :\n    n + 0 = n := by\n"
                 "  simp only [Nat.add_zero, Nat.zero_add, Nat.add_comm]\n\nend N\n")
    decls = declarations(decl_text)
    if len(decls) != 1 or not decls[0].startswith("@[simp]theoremt") or "endN" in decls[0]:
        fail(f"self-test: declarations: got {decls}")
    if len(docstrings(decl_text)) != 1:
        fail("self-test: docstrings")
    if not failures:
        ok("self-tests: import parsing, normalization, declaration and docstring splitting")


# ### Checks

def check_import_boundary():
    lib_files = [ROOT / "src/HilbertSmith.lean",
                 *sorted((ROOT / "src/HilbertSmith").rglob("*.lean"))]
    forbidden = HS_PROOF_ROOTS + BRIDGE_ROOTS
    bad = []
    for f in lib_files:
        for mod in imports_of(f):
            if mod.split(".")[0] in forbidden:
                bad.append(f"{f.relative_to(ROOT)}: import {mod}")
    if bad:
        fail("files of HilbertSmith import HS_proof, HSGeneral or HSBridge:\n  " + "\n  ".join(bad))
    else:
        ok(f"import boundary: none of the {len(lib_files)} files of HilbertSmith imports HS_proof, "
           "HSGeneral or HSBridge")


def check_coverage():
    src = ROOT / "src"
    seen, todo = set(), ["HilbertSmith"]
    while todo:
        mod = todo.pop()
        if mod in seen:
            continue
        seen.add(mod)
        path = src / (mod.replace(".", "/") + ".lean")
        if not path.exists():
            fail(f"module {mod} is imported but {path.relative_to(ROOT)} does not exist")
            continue
        todo.extend(m for m in imports_of(path) if m.split(".")[0] == "HilbertSmith")
    files = sorted((src / "HilbertSmith").rglob("*.lean"))
    missing = [f for f in files
               if ".".join(f.relative_to(src).with_suffix("").parts) not in seen]
    if missing:
        fail("not imported by src/HilbertSmith.lean:\n  "
             + "\n  ".join(str(f.relative_to(ROOT)) for f in missing))
    else:
        ok(f"coverage: all {len(files)} files under src/HilbertSmith are imported by "
           "src/HilbertSmith.lean")


def manifest_packages(text):
    return {p["name"]: p for p in json.loads(text)["packages"]}


def same_repo(url):
    return url is not None and url.removesuffix(".git").rstrip("/") == HS_PROOF_URL


def check_reference(repo, rev):
    """The source of `hsformal`, and HS_proof's libraries against our lists of its roots."""
    manifest = manifest_packages((ROOT / "lake-manifest.json").read_text())["hsformal"]
    lakefile = tomllib.loads((ROOT / "lakefile.toml").read_text())
    req = next((r for r in lakefile.get("require", []) if r.get("name") == "hsformal"), {})
    problems = []
    if not same_repo(manifest.get("url")):
        problems.append(f"lake-manifest.json url {manifest.get('url')}")
    if not same_repo(req.get("git")):
        problems.append(f"lakefile.toml git {req.get('git')}")
    if req.get("rev") != rev:
        problems.append(f"lakefile.toml rev {req.get('rev')} differs from the manifest's {rev}")
    if problems:
        fail(f"hsformal must come from {HS_PROOF_URL} at one revision: " + "; ".join(problems))
    else:
        ok(f"hsformal comes from {HS_PROOF_URL} at {rev} in both lakefile.toml and "
           "lake-manifest.json")
    theirs = tomllib.loads(git("show", f"{rev}:lakefile.toml", cwd=repo))
    libs = sorted(lib["name"] for lib in theirs.get("lean_lib", []))
    purity = (ROOT / "src/HSBridge/Purity.lean").read_text(encoding="utf-8")
    m = re.search(r"def hsProofRoots : List Name := \[([^\]]*)\]", purity)
    lean_roots = sorted(re.findall(r"`([\w.]+)", m.group(1))) if m else None
    if libs != sorted(HS_PROOF_ROOTS) or libs != lean_roots:
        fail(f"HS_proof's libraries {libs}; this script's roots {sorted(HS_PROOF_ROOTS)}; "
             f"Purity.lean's hsProofRoots {lean_roots}")
    else:
        ok(f"HS_proof's libraries at {rev[:7]} are exactly the roots counted as HS_proof here "
           f"and in Purity.lean: {', '.join(libs)}")


def hs_proof_repo(rev, tmp):
    """A git repository holding HS_proof's commit `rev`."""
    local = ROOT / ".lake/packages/hsformal"
    if (local / ".git").exists():
        probe = subprocess.run(["git", "cat-file", "-e", f"{rev}^{{commit}}"], cwd=local,
                               capture_output=True)
        if probe.returncode == 0:
            print(f"reading HS_proof {rev} from {local.relative_to(ROOT)}")
            return local
    print(f"fetching HS_proof {rev} from {HS_PROOF_URL}")
    repo = Path(tmp) / "hsformal"
    repo.mkdir()
    git("init", "-q", cwd=repo)
    git("fetch", "-q", "--depth", "1", HS_PROOF_URL, rev, cwd=repo)
    return repo


def check_pins(repo, rev):
    ours = manifest_packages((ROOT / "lake-manifest.json").read_text())
    theirs = manifest_packages(git("show", f"{rev}:lake-manifest.json", cwd=repo))
    for name in PINNED:
        a, b = ours.get(name, {}).get("rev"), theirs.get(name, {}).get("rev")
        if a is None or a != b:
            fail(f"pin of {name}: ours {a}, HS_proof's {b}")
        else:
            ok(f"pin of {name} equals HS_proof's: {a}")


def check_no_copying(repo, rev):
    tracked = [f for f in git("ls-files", "-z").split("\0") if f and (ROOT / f).is_file()]
    ns_hits, decl_hits = [], []
    for f in tracked:
        try:
            text = (ROOT / f).read_text(encoding="utf-8")
        except UnicodeDecodeError:
            continue
        if NAMESPACE_RE.search(text):
            ns_hits.append(f)
        if f.endswith(".lean") and DECL_IN_NAMESPACE_RE.search(text):
            decl_hits.append(f)
    if ns_hits or decl_hits:
        fail("tracked files open HS_proof's namespace or declare a name in it:\n  "
             + "\n  ".join(ns_hits + decl_hits))
    else:
        ok(f"no tracked file opens HS_proof's namespace, and no .lean file declares a name in it "
           f"({len(tracked)} files)")

    files, decls, docs = {}, {}, {}
    their_files = [f for f in git("ls-tree", "-r", "--name-only", "-z", rev, cwd=repo).split("\0")
                   if f.endswith(".lean")]
    for f in their_files:
        text = git("show", f"{rev}:{f}", cwd=repo, binary=True).decode("utf-8", "replace")
        norm = strip_ws(lex(text)[0])
        if norm:
            files.setdefault(digest(norm), f)
        for d in declarations(text):
            decls.setdefault(digest(d), f)
        for d in docstrings(text):
            docs.setdefault(digest(d), f)
    ours = [f for f in tracked if f.endswith(".lean")]
    copies, n_decls, n_docs = [], 0, 0
    for f in ours:
        text = (ROOT / f).read_text(encoding="utf-8")
        norm = strip_ws(lex(text)[0])
        if norm and digest(norm) in files:
            copies.append(f"{f} equals HS_proof's {files[digest(norm)]}")
        for d in declarations(text):
            n_decls += 1
            if digest(d) in decls:
                copies.append(f"{f}: a declaration equals one in HS_proof's {decls[digest(d)]}: "
                              f"{d[:60]}…")
        for d in docstrings(text):
            n_docs += 1
            if digest(d) in docs:
                copies.append(f"{f}: a docstring equals one in HS_proof's {docs[digest(d)]}: "
                              f"{d[:60]}…")
    if copies:
        fail("copies of HS_proof:\n  " + "\n  ".join(copies))
    else:
        ok(f"no copying: our {len(ours)} .lean files, {n_decls} top-level declarations (at least "
           f"{MIN_DECL_CHARS} characters without comments and whitespace) and {n_docs} docstrings "
           f"(at least {MIN_DOC_CHARS} characters, whitespace collapsed) match none of HS_proof's "
           f"{len(their_files)} files, {len(decls)} declarations and {len(docs)} docstrings at "
           f"{rev[:7]}, by digest")


def main():
    self_test()
    check_import_boundary()
    check_coverage()
    rev = manifest_packages((ROOT / "lake-manifest.json").read_text())["hsformal"]["rev"]
    with tempfile.TemporaryDirectory() as tmp:
        repo = hs_proof_repo(rev, tmp)
        check_reference(repo, rev)
        check_pins(repo, rev)
        check_no_copying(repo, rev)
    if failures:
        print(f"{len(failures)} check(s) failed")
        sys.exit(1)
    print("all route checks passed")


if __name__ == "__main__":
    main()
