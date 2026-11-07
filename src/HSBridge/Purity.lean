import Lean.Elab.Command

/-!
# The route-separation audit

One build holds both routes, so HS_proof's theorem `HSFormal.padicExclusion` is available to every
file that imports it, and it proves any statement of the form "hypotheses imply p-adic exclusion".
A theorem of OpenAI's route therefore means something only if its proof term does not use
HS_proof. The import boundary (the library `HilbertSmith` never imports `HSFormal`) is the first
guard; this file is the second, which checks proof terms.

## What is HS_proof

A module belongs to HS_proof if it is a module of HS_proof's package `hsformal`: its name has root
`HSFormal`, `Challenge`, `Solution`, `FCChallenge` or `FCSolution` (the package's five libraries).
A constant belongs to HS_proof if a module of HS_proof declares it. Constants are attributed by
module, not by name, so declarations outside the `HSFormal` namespace are caught too.

## Provenance

A name can be declared by several loaded modules: a theorem stated twice with the same type (as
HS_proof's `FCChallenge` and `FCSolution` do, the first with proof `sorry`), or an auxiliary lemma
that Lean realizes on demand in every module that needs it (such as the congruence lemma
`Homeomorph.addRight.congr_simp`). Lean then records only the lowest-indexed module holding a copy
(`Environment.getModuleIdxFor?`), while the kernel keeps the body of the last copy loaded. So the
audit looks at every module holding a copy, from the module data. If those modules are of different
kinds (HS_proof or not; importing HS_proof or not), `#assert_route_pure` fails with "ambiguous
provenance" instead of picking one.

## The walk

The audit walks every constant a declaration depends on, through types and values, as Lean core's
`CollectAxioms` does for `#print axioms`, reading the bodies the kernel holds. It enters a constant
if some module holding it imports HS_proof, directly or not, or is HS_proof; it does not enter a
constant all of whose modules are free of HS_proof. Such a module was elaborated and checked in an
environment without HS_proof, so its declarations have proofs that use no HS_proof constant.

What a success of `#assert_route_pure c` guarantees: in `c`'s proof term, with each constant of a
module free of HS_proof replaced by that module's own checked proof, no constant of HS_proof
occurs, except inside the declared discharges named in `allowing`. It errs on the safe side:
a constant of HS_proof that merely repeats a Mathlib fact (a realized congruence lemma, say) counts
as a use of HS_proof. It fails rather than guess when provenance is ambiguous, when a constant is
missing from the kernel environment, or when an import has no module index.

## Commands

* `HSBridge.Purity.audit`: the HS_proof constants a declaration reaches, and the entry points,
  i.e. those used directly by a constant that is not itself from HS_proof.
* `#route_report c`: prints, as an info message, how many HS_proof constants `c` reaches, grouped
  by module, together with its entry points into HS_proof.
* `#route_modules c front M₁ M₂ …`: prints the HS_proof modules whose constants `c` reaches, split
  into those in the import closure of `M₁, M₂, …` and the rest.
* `#assert_route_reaches c M` and `#assert_route_reaches_by_value c M`: fails unless `c`
  mentions, directly or not, a constant of a module under `M`; the second starts the walk from
  `c`'s value only, not its type and not the types of its leading binders.
* `#assert_import_boundary L`: fails if a module of the library `L` imported here imports
  HS_proof, directly or not. This is the import boundary, checked in the build.
* `#assert_route_pure c` and `#assert_route_pure c allowing a b`: fails, listing the entry points,
  if `c` reaches an HS_proof constant. The walk does not enter the allowed constants `a`, `b`, which
  must be declared discharges (`HSBridge.Purity.declaredDischarges`), such as the bridge
  discharging a published input from HS_proof.
* `#route_assumptions c flag f "note" … expanding S₁ S₂ …`: lists the fields of the structures
  that `c` takes as hypotheses, expanding fields whose type is one of the structures `Sᵢ`, with a
  note on each flagged field.

The file imports Lean core only. Its tests, including planted violations, are in
`HSBridge.PurityTest`.
-/

open Lean Elab Command Meta

namespace HSBridge.Purity

/-- The roots of the module names of HS_proof's package `hsformal`, one per library. -/
def hsProofRoots : List Name := [`HSFormal, `Challenge, `Solution, `FCChallenge, `FCSolution]

/-- Whether a module belongs to HS_proof's package `hsformal`. -/
def isHSProofModule (m : Name) : Bool :=
  hsProofRoots.contains m.getRoot

/-- **The declared discharges**: the only constants an allow-list may name. Each discharges a
published input of OpenAI's route from HS_proof's proof of it (PLAN §5). -/
def declaredDischarges : List Name := [`HSBridge.newmanInput]

/-- The name of the module with index `idx`. (`EnvironmentHeader.moduleNames` rebuilds the whole
array on each call, so it is avoided here.) -/
def moduleName (env : Environment) (idx : ModuleIdx) : Name :=
  env.header.modules[idx.toNat]!.module

/-- The first module that declares `c`, if `c` is imported. -/
def moduleOf? (env : Environment) (c : Name) : Option Name :=
  (env.getModuleIdxFor? c).map (moduleName env)

/-- What the audit knows about the loaded modules. -/
structure Provenance where
  /-- For each module, by index, whether it belongs to HS_proof. -/
  hs : Array Bool
  /-- For each module, by index, whether it belongs to HS_proof or imports one of its modules,
  directly or not. -/
  tainted : Array Bool
  /-- For each name declared by more than one loaded module, the modules after the first. -/
  copies : Std.HashMap Name (Array ModuleIdx)
  /-- Imports that have no module index (none are expected). -/
  unresolved : Array Name

/-- Computes the `Provenance` of the loaded modules. A module for which `tainted` is `false`
(Mathlib, TauCeti, Lean core, or the `HilbertSmith` library, for instance) was checked without
HS_proof, so the walk need not enter its constants. -/
def provenance (env : Environment) : Provenance := Id.run do
  let mods := env.header.modules
  let hs : Array Bool := mods.map fun m => isHSProofModule m.module
  let mut tainted := hs
  let mut unresolved : Array Name := #[]
  -- Propagate along imports until nothing changes. Modules are stored with their imports first,
  -- so one pass normally suffices; the loop does not rely on that.
  let mut changed := true
  while changed do
    changed := false
    for i in [0:mods.size] do
      if tainted[i]! then continue
      let mut reaches := false
      for imp in env.header.moduleData[i]!.imports do
        match env.getModuleIdx? imp.module with
        | some j => if tainted[j.toNat]! then reaches := true
        | none => unless unresolved.contains imp.module do unresolved := unresolved.push imp.module
      if reaches then
        tainted := tainted.set! i true
        changed := true
  -- Every module holding a copy of a name, beyond the first one Lean records.
  let mut copies : Std.HashMap Name (Array ModuleIdx) := {}
  for i in [0:mods.size] do
    for c in env.header.moduleData[i]!.constNames do
      if (env.getModuleIdxFor? c).map (·.toNat) != some i then
        copies := copies.insert c ((copies.getD c #[]).push i)
  return { hs, tainted, copies, unresolved }

namespace Provenance

/-- The loaded modules that declare `c`; empty for a constant of the current file. -/
def holders (P : Provenance) (env : Environment) (c : Name) : Array ModuleIdx :=
  match env.getModuleIdxFor? c with
  | some i => #[i] ++ P.copies.getD c #[]
  | none => #[]

/-- Whether `c` belongs to HS_proof: some module holding it does. -/
def isHS (P : Provenance) (env : Environment) (c : Name) : Bool :=
  (P.holders env c).any fun i => P.hs[i.toNat]!

/-- Whether the walk enters `c`: it is in the current file, or some module holding it is or
imports an HS_proof module. -/
def mayReach (P : Provenance) (env : Environment) (c : Name) : Bool :=
  let hs := P.holders env c
  hs.isEmpty || hs.any fun i => P.tainted[i.toNat]!

/-- Whether the modules holding `c` are of different kinds (HS_proof or not; importing HS_proof
or not), so that the module Lean records says nothing reliable about the body the kernel holds. -/
def isAmbiguous (P : Provenance) (env : Environment) (c : Name) : Bool :=
  let kind (i : ModuleIdx) := (P.hs[i.toNat]!, P.tainted[i.toNat]!)
  match (P.holders env c).toList with
  | i :: rest => rest.any fun j => kind j != kind i
  | [] => false

end Provenance

/-- The result of auditing one declaration. -/
structure Result where
  /-- The HS_proof constants reached, in no particular order. Without `descend`, only the entry
  points are reached. -/
  reached : NameSet := {}
  /-- The HS_proof constants used directly by a constant that is not from HS_proof. -/
  entries : NameSet := {}
  /-- The allowed constants met on the way (the walk does not enter them). -/
  allowedMet : NameSet := {}
  /-- The constants met whose modules are of different kinds (`Provenance.isAmbiguous`). -/
  ambiguous : NameSet := {}
  /-- The constants met that the kernel environment does not hold (none are expected). -/
  unknown : NameSet := {}
  /-- Imports without a module index (none are expected). -/
  unresolved : Array Name := #[]

-- Follows Lean core src/Lean/Util/CollectAxioms.lean (Copyright (c) 2020 Microsoft Corporation,
-- Apache-2.0).
/-- The constants a declaration mentions directly: those in its type and its value, and the
constructors of an inductive type, as in Lean core's `CollectAxioms`; `none` if the kernel
environment does not hold `c`. Constants are read from the kernel environment, which holds the
checked proof terms. -/
def directDeps (kenv : Kernel.Environment) (c : Name) : Option (Array Name) :=
  match kenv.find? c with
  | some (.axiomInfo v) => some v.type.getUsedConstants
  | some (.defnInfo v) => some (v.type.getUsedConstants ++ v.value.getUsedConstants)
  | some (.thmInfo v) => some (v.type.getUsedConstants ++ v.value.getUsedConstants)
  | some (.opaqueInfo v) => some (v.type.getUsedConstants ++ v.value.getUsedConstants)
  | some (.quotInfo _) => some #[]
  | some (.ctorInfo v) => some v.type.getUsedConstants
  | some (.recInfo v) => some v.type.getUsedConstants
  | some (.inductInfo v) => some (v.type.getUsedConstants ++ v.ctors.toArray)
  | none => none

/-- The constants in the value of `c` below its leading `fun` binders, whose types repeat the
hypotheses of `c`'s type; `none` if `c` has no value. -/
def valueDeps (kenv : Kernel.Environment) (c : Name) : Option (Array Name) :=
  let body : Expr → Expr := fun e => Id.run do
    let mut e := e
    while e.isLambda do e := e.bindingBody!
    return e
  match kenv.find? c with
  | some (.defnInfo v) => some (body v.value).getUsedConstants
  | some (.thmInfo v) => some (body v.value).getUsedConstants
  | some (.opaqueInfo v) => some (body v.value).getUsedConstants
  | _ => none

/-- Walks every constant that `root` depends on, transitively, without entering the constants in
`allow`, and records the HS_proof constants met. With `descend := false` the walk stops at the
first HS_proof constant on each path (enough to decide purity); with `descend := true` it continues
through HS_proof, to report everything reached there. With `valueOnly := true` the walk starts from
`valueDeps root` instead of `directDeps root`. Constants all of whose modules are free of HS_proof
are not entered (see `provenance`). -/
def audit (env : Environment) (root : Name) (allow : NameSet := {}) (descend := false)
    (valueOnly := false) : Result := Id.run do
  let kenv := env.checked.get
  let P := provenance env
  let mut res : Result := { unresolved := P.unresolved }
  let mut visited : NameSet := NameSet.empty.insert root
  if P.isAmbiguous env root then
    res := { res with ambiguous := res.ambiguous.insert root }
  let rootIsHS := P.isHS env root
  -- The root itself may be an HS_proof constant.
  if rootIsHS then
    res := { res with reached := res.reached.insert root, entries := res.entries.insert root }
  if (rootIsHS && !descend) || !P.mayReach env root then
    return res
  let rootDeps := if valueOnly then valueDeps kenv root else directDeps kenv root
  let some rootDeps := rootDeps | return { res with unknown := res.unknown.insert root }
  -- The work list holds a constant together with its direct dependencies.
  let mut stack : Array (Name × Array Name) := #[(root, rootDeps)]
  while h : stack.size > 0 do
    let (c, deps) := stack[stack.size - 1]
    stack := stack.pop
    let cIsHS := P.isHS env c
    for d in deps do
      if allow.contains d then
        res := { res with allowedMet := res.allowedMet.insert d }
        continue
      if visited.contains d then
        -- Already classified; record a new entry point if `c` is not from HS_proof.
        if !cIsHS && res.reached.contains d then
          res := { res with entries := res.entries.insert d }
        continue
      visited := visited.insert d
      if P.isAmbiguous env d then
        res := { res with ambiguous := res.ambiguous.insert d }
      let dIsHS := P.isHS env d
      if dIsHS then
        res := { res with reached := res.reached.insert d }
        unless cIsHS do
          res := { res with entries := res.entries.insert d }
      if !P.mayReach env d || (dIsHS && !descend) then continue
      match directDeps kenv d with
      | some ds => stack := stack.push (d, ds)
      | none => res := { res with unknown := res.unknown.insert d }
  return res

/-- The names in a `NameSet`, sorted. -/
def sorted (s : NameSet) : Array Name :=
  s.toArray.qsort Name.lt

/-- The HS_proof constants of `res`, counted by their module's first two name components
(for example `HSFormal.LTheory`), sorted by module. -/
def countByModule (env : Environment) (res : Result) : Array (Name × Nat) := Id.run do
  let mut counts : Std.HashMap Name Nat := {}
  for c in res.reached do
    let m := (moduleOf? env c).getD .anonymous
    let key := match m.components with
      | a :: b :: _ :: _ => a ++ b
      | _ => m
    counts := counts.insert key (counts.getD key 0 + 1)
  return counts.toArray.qsort fun a b => Name.lt a.1 b.1

/-- Resolves an identifier to exactly one constant, as `#print axioms` does. -/
def resolveConst (id : Ident) : CommandElabM Name :=
  liftCoreM <| realizeGlobalConstNoOverloadWithInfo id

/-- The names, one per indented line. -/
def nameLines (names : Array Name) : MessageData :=
  MessageData.joinSep (names.toList.map fun n => m!"\n  {n}") ""

/-- Throws if the walk met a constant of ambiguous provenance, a constant missing from the kernel
environment, or an import without a module index. -/
def throwIfUndecided (c : Name) (res : Result) : CommandElabM Unit := do
  unless res.unresolved.isEmpty do
    throwError m!"route audit: imports without a module index:" ++ nameLines res.unresolved
  unless res.unknown.isEmpty do
    throwError m!"route audit: '{c}' depends on constants missing from the kernel environment:" ++
      nameLines (sorted res.unknown)
  unless res.ambiguous.isEmpty do
    throwError m!"route audit: '{c}' depends on constants of ambiguous provenance, declared by \
      modules of different kinds:" ++ nameLines (sorted res.ambiguous)

/-- `#route_report c` prints the HS_proof constants that `c` depends on, counted by module, its
entry points into HS_proof, and any constants of ambiguous provenance met. It never fails. -/
syntax (name := routeReport) "#route_report " ident : command

@[command_elab routeReport]
def elabRouteReport : CommandElab
  | `(#route_report $id) => do
    let c ← resolveConst id
    let env ← getEnv
    let res := audit env c (descend := true)
    if res.reached.isEmpty then
      logInfo m!"route audit: '{c}' depends on no constant from HS_proof"
    else
      let counts := countByModule env res
      let lines := counts.toList.map fun (m, k) => m!"\n  {m}: {k}"
      let ambiguous := if res.ambiguous.isEmpty then m!"" else
        m!"\nof ambiguous provenance:" ++ nameLines (sorted res.ambiguous)
      logInfo <| m!"route audit: '{c}' depends on {res.reached.size} constants from HS_proof; \
        by module:" ++ MessageData.joinSep lines "" ++
        m!"\nentry points into HS_proof:" ++ nameLines (sorted res.entries) ++ ambiguous
  | _ => throwUnsupportedSyntax

/-- `#assert_route_pure c` fails, listing the entry points, if `c` depends on any constant from
HS_proof. With `allowing a b ...`, the walk does not enter `a`, `b`, ...; each must be one of the
declared discharges (`HSBridge.Purity.declaredDischarges`), and a constant that `c` reaches, or the
command fails, so that an allow-list can neither admit HS_proof nor go stale unnoticed. -/
syntax (name := assertRoutePure) "#assert_route_pure " ident (" allowing" (ppSpace ident)+)? :
  command

@[command_elab assertRoutePure]
def elabAssertRoutePure : CommandElab
  | `(#assert_route_pure $id $[allowing $allowed*]?) => do
    let c ← resolveConst id
    let allowedNames ← (allowed.getD #[]).mapM resolveConst
    let env ← getEnv
    let P := provenance env
    let fromHS := allowedNames.filter (P.isHS env)
    unless fromHS.isEmpty do
      throwError m!"route audit: an allow-list may not name constants of HS_proof:" ++
        nameLines fromHS
    let undeclared := allowedNames.filter (!declaredDischarges.contains ·)
    unless undeclared.isEmpty do
      throwError m!"route audit: not declared discharges (HSBridge.Purity.declaredDischarges):" ++
        nameLines undeclared
    let allow := allowedNames.foldl (init := {}) NameSet.insert
    let res := audit env c allow
    let unused := allowedNames.filter fun a => !res.allowedMet.contains a
    unless unused.isEmpty do
      throwError m!"route audit: '{c}' does not depend on the allowed constants:" ++
        nameLines unused
    throwIfUndecided c res
    unless res.reached.isEmpty do
      throwError m!"route audit: '{c}' depends on HS_proof; entry points:" ++
        nameLines (sorted res.entries)
    if allowedNames.isEmpty then
      logInfo m!"route audit: '{c}' depends on no constant from HS_proof"
    else
      logInfo <| m!"route audit: '{c}' depends on no constant from HS_proof except through:" ++
        nameLines allowedNames
  | _ => throwUnsupportedSyntax

/-- `#assert_route_reaches c M` fails unless `c` mentions, directly or not, some constant declared
in a module whose name starts with `M` (for example `HSFormal.LTheory`). It checks the positive half
of a comparison. A constant mentioned only in `c`'s type counts. -/
syntax (name := assertRouteReaches) "#assert_route_reaches " ident ident : command

/-- `#assert_route_reaches_by_value c M` is `#assert_route_reaches c M` with the walk started from
`c`'s value, below its leading binders, so that the hypotheses of `c` do not count by themselves
(the types of the theorems its proof applies still do). -/
syntax (name := assertRouteReachesByValue) "#assert_route_reaches_by_value " ident ident : command

/-- The common part of `#assert_route_reaches` and `#assert_route_reaches_by_value`. -/
def runAssertRouteReaches (id pre : Ident) (valueOnly : Bool) : CommandElabM Unit := do
  let c ← resolveConst id
  let env ← getEnv
  let res := audit env c (descend := true) (valueOnly := valueOnly)
  let hits := res.reached.toArray.filter fun d =>
    match moduleOf? env d with
    | some m => pre.getId.isPrefixOf m
    | none => false
  let start := if valueOnly then "the value of " else ""
  if hits.isEmpty then
    throwError "route audit: {start}'{c}' depends on no constant from modules under \
      '{pre.getId}'"
  logInfo m!"route audit: {start}'{c}' depends on constants from modules under '{pre.getId}'"

@[command_elab assertRouteReaches]
def elabAssertRouteReaches : CommandElab
  | `(#assert_route_reaches $id $pre) => runAssertRouteReaches id pre false
  | _ => throwUnsupportedSyntax

@[command_elab assertRouteReachesByValue]
def elabAssertRouteReachesByValue : CommandElab
  | `(#assert_route_reaches_by_value $id $pre) => runAssertRouteReaches id pre true
  | _ => throwUnsupportedSyntax

/-- The HS_proof modules among the import closure of `roots`, which must all be loaded. -/
def importClosure (env : Environment) (roots : Array Name) : Except MessageData NameSet := do
  let mut seen : NameSet := {}
  let mut todo := roots
  while h : todo.size > 0 do
    let m := todo[todo.size - 1]
    todo := todo.pop
    if seen.contains m then continue
    let some i := env.getModuleIdx? m | throw m!"route audit: module '{m}' is not loaded here"
    seen := seen.insert m
    for imp in env.header.moduleData[i.toNat]!.imports do
      todo := todo.push imp.module
  return (seen.toArray.filter isHSProofModule).foldl NameSet.insert {}

/-- `#route_modules c front M₁ M₂ …` prints the HS_proof modules declaring a constant that `c`
reaches, split into those in the import closure of `M₁, M₂, …` (the front) and the rest (the back
end), with counts. It never fails, unless a module `Mᵢ` is not loaded. -/
syntax (name := routeModules) "#route_modules " ident ppSpace &"front" (ppSpace ident)+ : command

@[command_elab routeModules]
def elabRouteModules : CommandElab
  | `(#route_modules $id front $roots*) => do
    let c ← resolveConst id
    let env ← getEnv
    let frontMods ← match importClosure env (roots.map (·.getId)) with
      | .ok s => pure s
      | .error e => throwError e
    let res := audit env c (descend := true)
    let touched : NameSet := res.reached.toArray.foldl (init := {}) fun s d =>
      match moduleOf? env d with
      | some m => s.insert m
      | none => s
    let inFront := (sorted touched).filter frontMods.contains
    let back := (sorted touched).filter (!frontMods.contains ·)
    logInfo <| m!"route modules: '{c}' reaches constants of {touched.size} HS_proof modules; \
      {inFront.size} of them in the front ({frontMods.size} modules), {back.size} in the back end.\
      \nfront:" ++ nameLines inFront ++ m!"\nback end:" ++ nameLines back
  | _ => throwUnsupportedSyntax

/-- `#assert_import_boundary L` fails, listing them, if some imported module whose name has root `L`
imports a module of HS_proof, directly or not. It checks the modules imported into the current
file, so a file that imports a library's root module checks the whole library. -/
syntax (name := assertImportBoundary) "#assert_import_boundary " ident : command

@[command_elab assertImportBoundary]
def elabAssertImportBoundary : CommandElab
  | `(#assert_import_boundary $lib) => do
    let env ← getEnv
    let P := provenance env
    unless P.unresolved.isEmpty do
      throwError m!"import boundary: imports without a module index:" ++ nameLines P.unresolved
    let mods := env.header.modules.map (·.module)
    let inLib := (List.range mods.size).filter fun i => mods[i]!.getRoot == lib.getId
    if inLib.isEmpty then
      throwError "import boundary: no module of '{lib.getId}' is imported here"
    let offenders := (inLib.filter fun i => P.tainted[i]!).map fun i => mods[i]!
    unless offenders.isEmpty do
      throwError m!"import boundary: these modules of '{lib.getId}' import HS_proof:" ++
        nameLines offenders.toArray
    logInfo m!"import boundary: no imported module of '{lib.getId}' imports HS_proof"
  | _ => throwUnsupportedSyntax

/-- The structure that `type` is an instance of, if its head is a structure (not a class). -/
def structureOf? (env : Environment) (type : Expr) : Option Name :=
  match type.getAppFn with
  | .const s _ => if isStructure env s && !isClass env s then some s else none
  | _ => none

/-- `#route_assumptions c flag f₁ "note₁" … expanding S₁ S₂ …` lists, for each hypothesis of `c`
whose type is a structure, that structure's fields (`getStructureFieldsFlattened`). A field whose
type, below its `∀` binders, is one of the structures `Sᵢ` is followed by `Sᵢ`'s fields, indented.
A field named `fᵢ` is followed by its note. Under `#guard_msgs`, adding or removing a field changes
the message and so fails the build. -/
syntax (name := routeAssumptions) "#route_assumptions " ident
  (ppSpace &"flag" ppSpace ident ppSpace str)* (ppSpace &"expanding" (ppSpace ident)+)? : command

@[command_elab routeAssumptions]
def elabRouteAssumptions : CommandElab
  | `(#route_assumptions $id $[flag $fs $notes]* $[expanding $exps*]?) => do
    let c ← resolveConst id
    let env ← getEnv
    let expand ← (exps.getD #[]).mapM resolveConst
    let flags := (fs.map (·.getId)).zip (notes.map (·.getString))
    let fieldLines (indent : String) (s : Name) : MetaM (Array MessageData) := do
      let mut lines := #[]
      for f in getStructureFieldsFlattened env s (includeSubobjectFields := false) do
        let sub ← match getProjFnForField? env s f >>= env.find? with
          | some info => forallTelescope info.type fun _ body => pure (structureOf? env body)
          | none => pure none
        let sub := sub.filter expand.contains
        let mut line := m!"\n{indent}{f}"
        if let some t := sub then
          line := line ++ m!" ({t}, expanded)"
        if let some (_, note) := flags.find? (·.1 == f) then
          line := line ++ m!"\n{indent}  flagged: {note}"
        lines := lines.push line
        if let some t := sub then
          for f' in getStructureFieldsFlattened env t (includeSubobjectFields := false) do
            lines := lines.push m!"\n{indent}  {f'}"
      return lines
    let msg ← liftTermElabM do
      let some info := env.find? c | throwError "unknown constant '{c}'"
      forallTelescope info.type fun xs _ => do
        let mut msg := m!"route assumptions of '{c}':"
        for x in xs do
          let t ← inferType x
          let some s := structureOf? env t | continue
          let lines ← fieldLines "  " s
          msg := msg ++ m!"\n{← ppExpr x} : {← ppExpr t}" ++ MessageData.joinSep lines.toList ""
        return msg
    logInfo msg
  | _ => throwUnsupportedSyntax

end HSBridge.Purity
