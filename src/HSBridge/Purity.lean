import Lean.Elab.Command

/-!
# The route-separation audit

One build holds both routes, so HS_proof's theorem `HSFormal.padicExclusion` is available to every
file that imports it, and it proves any statement of the form "hypotheses imply p-adic exclusion".
A theorem of OpenAI's route therefore means something only if its proof term does not use
HS_proof. The import boundary (the library `HilbertSmith` never imports `HSFormal`) is the first
guard; this file is the second, which checks proof terms.

The audit walks every constant a declaration depends on, through types and values, as Lean core's
`CollectAxioms` does for `#print axioms`, and records which of them were declared in a module of
HS_proof's library `HSFormal`. Constants are attributed to `HSFormal` by the module that declares
them, not by their names, so that declarations outside the `HSFormal` namespace are caught too.
This errs on the safe side: an auxiliary lemma that Lean generates on demand for a Mathlib
definition (such as the congruence lemma `Homeomorph.addRight.congr_simp`) belongs to the module
where it was first generated, which may be an `HSFormal` module, and then counts as `HSFormal`.
The audit can thus report a use of `HSFormal` that is harmless, but it cannot miss one.

The walk does not enter constants of modules that do not import `HSFormal`, directly or not:
such a constant can only mention constants of its own module and the modules it imports. This
keeps the walk to the current file and `HSFormal` itself.

* `HSBridge.Purity.audit`: the `HSFormal` constants a declaration reaches, and the entry points,
  i.e. those used directly by a constant that is not itself from `HSFormal`.
* `#route_report c`: prints, as an info message, how many `HSFormal` constants `c` reaches, grouped
  by module, together with its entry points into `HSFormal`.
* `#assert_route_reaches c M`: fails unless `c` reaches some constant of a module under `M`.
* `#assert_import_boundary L`: fails if a module of the library `L` imported here imports
  `HSFormal`, directly or not. This is the import boundary, checked in the build.
* `#assert_route_pure c` and `#assert_route_pure c allowing a b`: fails, listing the entry points,
  if `c` reaches an `HSFormal` constant. The walk does not enter the allowed constants `a`, `b`, so
  they may use `HSFormal` (for example the bridge discharging a published input from HS_proof)
  while every other path from `c` may not.

The file imports Lean core only. Its tests, including a planted violation, are in
`HSBridge.PurityTest`.
-/

open Lean Elab Command

namespace HSBridge.Purity

/-- The name of the module with index `idx`. (`EnvironmentHeader.moduleNames` rebuilds the whole
array on each call, so it is avoided here.) -/
def moduleName (env : Environment) (idx : ModuleIdx) : Name :=
  env.header.modules[idx.toNat]!.module

/-- The module that declares `c`, if `c` is imported. -/
def moduleOf? (env : Environment) (c : Name) : Option Name :=
  (env.getModuleIdxFor? c).map (moduleName env)

/-- Whether the constant `c` was declared in a module of HS_proof's library, i.e. a module whose
name has root `HSFormal`. Constants of the current file count as not from `HSFormal`. -/
def isHSFormalConst (env : Environment) (c : Name) : Bool :=
  match moduleOf? env c with
  | some m => m.getRoot == `HSFormal
  | none => false

/-- For each imported module, by index, whether it is an `HSFormal` module or imports one,
directly or not. A constant of a module for which this is `false` (Mathlib, TauCeti, Lean core, or
the `HilbertSmith` library, for instance) can only mention constants of that module and of the
modules it imports, so it cannot reach `HSFormal`, and the walk need not enter it. -/
def reachesHSFormalModules (env : Environment) : Array Bool := Id.run do
  let mods := env.header.modules
  let mut flags : Array Bool := mods.map fun m => m.module.getRoot == `HSFormal
  -- Propagate along imports until nothing changes. Modules are stored with their imports first,
  -- so one pass normally suffices; the loop does not rely on that.
  let mut changed := true
  while changed do
    changed := false
    for i in [0:mods.size] do
      if flags[i]! then continue
      let imports := env.header.moduleData[i]!.imports
      if imports.any fun imp =>
          match env.getModuleIdx? imp.module with
          | some j => flags[j.toNat]!
          | none => false then
        flags := flags.set! i true
        changed := true
  return flags

/-- The result of auditing one declaration. -/
structure Result where
  /-- The `HSFormal` constants reached, in no particular order. Without `descend`, only the
  entry points are reached. -/
  reached : NameSet := {}
  /-- The `HSFormal` constants used directly by a constant that is not from `HSFormal`. -/
  entries : NameSet := {}
  /-- The allowed constants met on the way (the walk does not enter them). -/
  allowedMet : NameSet := {}

/-- The constants a declaration mentions directly: those in its type and its value, and the
constructors of an inductive type, as in Lean core's `CollectAxioms`. Constants are read from the
kernel environment, which holds the checked proof terms. -/
def directDeps (kenv : Kernel.Environment) (c : Name) : Array Name :=
  match kenv.find? c with
  | some (.axiomInfo v) => v.type.getUsedConstants
  | some (.defnInfo v) => v.type.getUsedConstants ++ v.value.getUsedConstants
  | some (.thmInfo v) => v.type.getUsedConstants ++ v.value.getUsedConstants
  | some (.opaqueInfo v) => v.type.getUsedConstants ++ v.value.getUsedConstants
  | some (.quotInfo _) => #[]
  | some (.ctorInfo v) => v.type.getUsedConstants
  | some (.recInfo v) => v.type.getUsedConstants
  | some (.inductInfo v) => v.type.getUsedConstants ++ v.ctors.toArray
  | none => #[]

/-- Walks every constant that `root` depends on, transitively, without entering the constants in
`allow`, and records the `HSFormal` constants met. With `descend := false` the walk stops at the
first `HSFormal` constant on each path (enough to decide purity); with `descend := true` it
continues through `HSFormal`, to report everything reached there. Constants of modules that cannot
reach `HSFormal` (see `reachesHSFormalModules`) are not entered. -/
def audit (env : Environment) (root : Name) (allow : NameSet := {}) (descend := false) :
    Result := Id.run do
  let kenv := env.checked.get
  let tainted := reachesHSFormalModules env
  let mayReach (c : Name) : Bool :=
    match env.getModuleIdxFor? c with
    | some idx => tainted[idx.toNat]!
    | none => true
  let mut visited : NameSet := NameSet.empty.insert root
  let mut stack : Array Name := if mayReach root then #[root] else #[]
  let mut res : Result := {}
  -- The root itself may be an `HSFormal` constant.
  if isHSFormalConst env root then
    res := { res with reached := res.reached.insert root, entries := res.entries.insert root }
    unless descend do stack := #[]
  while h : stack.size > 0 do
    let c := stack[stack.size - 1]
    stack := stack.pop
    let cIsHS := isHSFormalConst env c
    for d in directDeps kenv c do
      if allow.contains d then
        res := { res with allowedMet := res.allowedMet.insert d }
        continue
      let dIsHS := isHSFormalConst env d
      if dIsHS then
        res := { res with reached := res.reached.insert d }
        unless cIsHS do
          res := { res with entries := res.entries.insert d }
      if visited.contains d || !mayReach d || (dIsHS && !descend) then continue
      visited := visited.insert d
      stack := stack.push d
  return res

/-- The names in a `NameSet`, sorted. -/
def sorted (s : NameSet) : Array Name :=
  s.toArray.qsort Name.lt

/-- The `HSFormal` constants of `res`, counted by their module's first two name components
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

/-- `#route_report c` prints the `HSFormal` constants that `c` depends on, counted by module, and
its entry points into `HSFormal`. It never fails. -/
syntax (name := routeReport) "#route_report " ident : command

/-- `#assert_route_pure c` fails, listing the entry points, if `c` depends on any constant from
HS_proof's library `HSFormal`. With `allowing a b ...`, the walk does not enter `a`, `b`, ...; each
must be a constant that `c` reaches, or the command fails, so that an allow-list cannot go stale
unnoticed. -/
syntax (name := assertRoutePure) "#assert_route_pure " ident (" allowing" (ppSpace ident)+)? :
  command

@[command_elab routeReport]
def elabRouteReport : CommandElab
  | `(#route_report $id) => do
    let c ← resolveConst id
    let env ← getEnv
    let res := audit env c (descend := true)
    if res.reached.isEmpty then
      logInfo m!"route audit: '{c}' depends on no constant from HSFormal"
    else
      let counts := countByModule env res
      let lines := counts.toList.map fun (m, k) => m!"\n  {m}: {k}"
      logInfo <| m!"route audit: '{c}' depends on {res.reached.size} constants from HSFormal; \
        by module:" ++ MessageData.joinSep lines "" ++
        m!"\nentry points into HSFormal:" ++ nameLines (sorted res.entries)
  | _ => throwUnsupportedSyntax

@[command_elab assertRoutePure]
def elabAssertRoutePure : CommandElab
  | `(#assert_route_pure $id $[allowing $allowed*]?) => do
    let c ← resolveConst id
    let allowedNames ← (allowed.getD #[]).mapM resolveConst
    let allow := allowedNames.foldl (init := {}) NameSet.insert
    let env ← getEnv
    let res := audit env c allow
    let unused := allowedNames.filter fun a => !res.allowedMet.contains a
    unless unused.isEmpty do
      throwError m!"route audit: '{c}' does not depend on the allowed constants:" ++
        nameLines unused
    unless res.reached.isEmpty do
      throwError m!"route audit: '{c}' depends on HSFormal; entry points:" ++
        nameLines (sorted res.entries)
    if allowedNames.isEmpty then
      logInfo m!"route audit: '{c}' depends on no constant from HSFormal"
    else
      logInfo <| m!"route audit: '{c}' depends on no constant from HSFormal except through:" ++
        nameLines allowedNames
  | _ => throwUnsupportedSyntax

/-- `#assert_route_reaches c M` fails unless `c` depends on some constant declared in a module
whose name starts with `M` (for example `HSFormal.LTheory`). It checks the positive half of a
comparison: that a theorem really goes through the part of `HSFormal` it is said to use. -/
syntax (name := assertRouteReaches) "#assert_route_reaches " ident ident : command

@[command_elab assertRouteReaches]
def elabAssertRouteReaches : CommandElab
  | `(#assert_route_reaches $id $pre) => do
    let c ← resolveConst id
    let env ← getEnv
    let res := audit env c (descend := true)
    let hits := res.reached.toArray.filter fun d =>
      match moduleOf? env d with
      | some m => pre.getId.isPrefixOf m
      | none => false
    if hits.isEmpty then
      throwError "route audit: '{c}' depends on no constant from modules under '{pre.getId}'"
    logInfo m!"route audit: '{c}' depends on {hits.size} constants from modules under \
      '{pre.getId}'"
  | _ => throwUnsupportedSyntax

/-- `#assert_import_boundary L` fails, listing them, if some imported module whose name has root `L`
imports a module of `HSFormal`, directly or not. It checks the modules imported into the current
file, so a file that imports a library's root module checks the whole library. -/
syntax (name := assertImportBoundary) "#assert_import_boundary " ident : command

@[command_elab assertImportBoundary]
def elabAssertImportBoundary : CommandElab
  | `(#assert_import_boundary $lib) => do
    let env ← getEnv
    let tainted := reachesHSFormalModules env
    let mods := env.header.modules.map (·.module)
    let inLib := (List.range mods.size).filter fun i => mods[i]!.getRoot == lib.getId
    if inLib.isEmpty then
      throwError "import boundary: no module of '{lib.getId}' is imported here"
    let offenders := (inLib.filter fun i => tainted[i]!).map fun i => mods[i]!
    unless offenders.isEmpty do
      throwError m!"import boundary: these modules of '{lib.getId}' import HSFormal:" ++
        nameLines offenders.toArray
    logInfo m!"import boundary: no imported module of '{lib.getId}' imports HSFormal"
  | _ => throwUnsupportedSyntax

end HSBridge.Purity
