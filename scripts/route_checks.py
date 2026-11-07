#!/usr/bin/env python3
"""Route-separation checks of PLAN section 5 that need no Lean build.

1. Import boundary: no file of the library `HilbertSmith` imports a module of HS_proof.
2. Coverage: every `src/HilbertSmith/**/*.lean` is imported, transitively, by
   `src/HilbertSmith.lean`, so the in-build check `#assert_import_boundary HilbertSmith` sees it.
3. Pin equality: the `mathlib` and `TauCeti` revisions in `lake-manifest.json` equal those in
   HS_proof's `lake-manifest.json` at the revision pinned for `hsformal`.
4. No copying: no tracked file contains the namespace declaration of HS_proof's library, and no
   tracked `.lean` file equals an HS_proof `.lean` file after comments and whitespace are removed.

HS_proof is read with git at the pinned revision: from `.lake/packages/hsformal` if that checkout
has the commit (a local build), otherwise fetched from GitHub into a temporary directory.

Run from the repository root: `python3 scripts/route_checks.py`. Exits 1 if a check fails.
"""

import hashlib
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
# The module roots of HS_proof's package `hsformal`, one per library.
HS_PROOF_ROOTS = ("HSFormal", "Challenge", "Solution", "FCChallenge", "FCSolution")
# Split so that this file does not match its own check.
FORBIDDEN_NAMESPACE = "namespace " + "HSFormal"
PINNED = ("mathlib", "TauCeti")

failures = []


def fail(msg):
    failures.append(msg)
    print(f"FAIL: {msg}")


def ok(msg):
    print(f"ok: {msg}")


def git(*args, cwd=ROOT, binary=False):
    out = subprocess.run(["git", *args], cwd=cwd, check=True, capture_output=True)
    return out.stdout if binary else out.stdout.decode()


def imports_of(path):
    """The modules a Lean file imports (header `import` lines only)."""
    mods = []
    for line in path.read_text(encoding="utf-8").splitlines():
        m = re.match(r"^\s*(?:public\s+)?import\s+(?:all\s+)?([\w.']+)", line)
        if m:
            mods.append(m.group(1))
    return mods


def check_import_boundary():
    lib_files = [ROOT / "src/HilbertSmith.lean",
                 *sorted((ROOT / "src/HilbertSmith").rglob("*.lean"))]
    bad = []
    for f in lib_files:
        for mod in imports_of(f):
            if mod.split(".")[0] in HS_PROOF_ROOTS:
                bad.append(f"{f.relative_to(ROOT)}: import {mod}")
    if bad:
        fail("files of HilbertSmith import HS_proof:\n  " + "\n  ".join(bad))
    else:
        ok(f"import boundary: none of the {len(lib_files)} files of HilbertSmith imports HS_proof")


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


def manifest_revs(text):
    return {p["name"]: p["rev"] for p in json.loads(text)["packages"]}


def hs_proof_repo(rev, tmp):
    """A git repository holding HS_proof's commit `rev`."""
    local = ROOT / ".lake/packages/hsformal"
    if (local / ".git").exists():
        probe = subprocess.run(["git", "cat-file", "-e", f"{rev}^{{commit}}"], cwd=local,
                               capture_output=True)
        if probe.returncode == 0:
            print(f"reading HS_proof {rev} from {local.relative_to(ROOT)}")
            return local
    url = next(p["url"] for p in json.loads((ROOT / "lake-manifest.json").read_text())["packages"]
               if p["name"] == "hsformal")
    print(f"fetching HS_proof {rev} from {url}")
    repo = Path(tmp) / "hsformal"
    repo.mkdir()
    git("init", "-q", cwd=repo)
    git("fetch", "-q", "--depth", "1", url, rev, cwd=repo)
    return repo


def check_pins(repo, rev):
    ours = manifest_revs((ROOT / "lake-manifest.json").read_text())
    theirs = manifest_revs(git("show", f"{rev}:lake-manifest.json", cwd=repo))
    for name in PINNED:
        if ours.get(name) != theirs.get(name):
            fail(f"pin of {name}: ours {ours.get(name)}, HS_proof's {theirs.get(name)}")
        else:
            ok(f"pin of {name} equals HS_proof's: {ours[name]}")


def normalize_lean(text):
    """The text without comments (`--` lines, nested `/- -/` blocks) and without whitespace."""
    out, i, n, depth, in_str = [], 0, len(text), 0, False
    while i < n:
        c, two = text[i], text[i:i + 2]
        if depth:
            if two == "/-":
                depth, i = depth + 1, i + 2
            elif two == "-/":
                depth, i = depth - 1, i + 2
            else:
                i += 1
        elif in_str:
            out.append(c)
            if c == "\\" and i + 1 < n:
                out.append(text[i + 1])
                i += 2
                continue
            in_str = c != '"'
            i += 1
        elif two == "/-":
            depth, i = 1, i + 2
        elif two == "--":
            j = text.find("\n", i)
            i = n if j < 0 else j
        else:
            in_str = c == '"'
            out.append(c)
            i += 1
    return re.sub(r"\s+", "", "".join(out))


def digest(text):
    norm = normalize_lean(text)
    return hashlib.sha256(norm.encode()).hexdigest() if norm else None


def check_no_copying(repo, rev):
    tracked = git("ls-files", "-z").split("\0")
    hits = []
    for f in tracked:
        p = ROOT / f
        if not f or not p.is_file():
            continue
        try:
            if FORBIDDEN_NAMESPACE in p.read_text(encoding="utf-8"):
                hits.append(f)
        except UnicodeDecodeError:
            continue
    if hits:
        fail(f"tracked files contain '{FORBIDDEN_NAMESPACE}':\n  " + "\n  ".join(hits))
    else:
        ok(f"no tracked file contains '{FORBIDDEN_NAMESPACE}'")

    theirs = {}
    for f in git("ls-tree", "-r", "--name-only", "-z", rev, cwd=repo).split("\0"):
        if f.endswith(".lean"):
            text = git("show", f"{rev}:{f}", cwd=repo, binary=True).decode("utf-8", "replace")
            d = digest(text)
            if d:
                theirs.setdefault(d, f)
    ours = [f for f in tracked if f.endswith(".lean")]
    copies = []
    for f in ours:
        d = digest((ROOT / f).read_text(encoding="utf-8"))
        if d and d in theirs:
            copies.append(f"{f} matches HS_proof's {theirs[d]}")
    if copies:
        fail("files equal to HS_proof files up to comments and whitespace:\n  "
             + "\n  ".join(copies))
    else:
        ok(f"no copying: none of our {len(ours)} .lean files matches one of HS_proof's "
           f"{len(theirs)} by normalized hash")


def main():
    check_import_boundary()
    check_coverage()
    rev = manifest_revs((ROOT / "lake-manifest.json").read_text())["hsformal"]
    with tempfile.TemporaryDirectory() as tmp:
        repo = hs_proof_repo(rev, tmp)
        check_pins(repo, rev)
        check_no_copying(repo, rev)
    if failures:
        print(f"{len(failures)} check(s) failed")
        sys.exit(1)
    print("all route checks passed")


if __name__ == "__main__":
    main()
