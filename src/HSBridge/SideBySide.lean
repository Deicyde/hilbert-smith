import HSBridge.Purity
import HSBridge.Statements
import HSFormal.HilbertSmith
import HSFormal.HilbertSmithModel
import HSGeneral.Padic
import HilbertSmith.Interface.Main

/-!
# The two routes side by side

Both routes conclude p-adic exclusion for second-countable manifolds, the statement
`HilbertSmith.Statements.PadicExclusion` (OpenAI's Theorem 1.2): HS_proof's route unconditionally,
OpenAI's from `OAIInterface` and `LocalInputs`, neither of which is discharged yet, and Newman's
theorem `HilbertSmith.NewmanInput`.

Without second countability (`HilbertSmith.Statements.PadicExclusionNoSC`) the two routes get
there differently. HS_proof's Lean theorem is stated with second countability; HS_proof's paper
removes it by a global invariant exhaustion, which `HSGeneral.padicExclusionNoSC` formalizes,
unconditionally, on top of HS_proof's theorem. OpenAI's Proposition 5.1 never leaves one chart, so
OpenAI's route concludes the statement without second countability directly, from `OAIInterface`
and `LocalInputs` alone (`oai_route_noSC`, with Newman's theorem discharged from HS_proof by
`HSBridge.newmanInput`).

* `HSBridge.statements_agree` (in `HSBridge.Statements`): it is HS_proof's
  `HSFormal.PadicExclusion`, by `Iff.rfl`.
* `HSBridge.hs_route`: HS_proof's proof, unconditional, and `HSBridge.hs_route_univ` in every
  universe.
* `HSBridge.hs_route_of_inputs`: HS_proof's proof at its interface level,
  `HSFormal.padicExclusion_of_inputs`: from its L-theory interface `HSFormal.LTheory.LowerLTheory`
  and Newman's theorem `HSFormal.NewmanPrimeOrder`.
* `HSBridge.oai_route`: OpenAI's proof at its interface level,
  `HilbertSmith.Interface.padicExclusion_of_oaiInterface`: from `OAIInterface` (the Witt groups of
  sheaves, as §§5–6 use them), `LocalInputs` (the topology of §5 still assumed) and
  `HilbertSmith.NewmanInput` (Newman's theorem, which Proposition 5.1 uses).
* `HSBridge.oai_route_noSC`: OpenAI's route without second countability,
  `HilbertSmith.Interface.padicExclusion_of_oaiInterface_noSC`, from `OAIInterface` and
  `LocalInputs` alone, with Newman's theorem discharged from HS_proof by `HSBridge.newmanInput`.

## What each route assumes

For the second-countable statement, the same conclusion with two sets of hypotheses
(`hs_route_of_inputs` against `oai_route`), and an asymmetry:

* HS_proof discharges both of its hypotheses: `LowerLTheory` by its model
  `HSFormal.LTheory.lowerLModel` (used in `HSFormal.padicExclusion_of_model`), and Newman's
  theorem by `HSFormal.Newman.newmanPrimeOrder`.
* OpenAI's route discharges neither of its interfaces yet. `OAIInterface` needs the sheaf model of
  §§2–4. `LocalInputs` collects what is still assumed from §5: the orientation facts
  (`Orientation`), Lemma 5.3 in pinch form (`AveragedTest`), and Lemmas 5.4 and 5.5 combined
  (`OrbitNull`). The rest of §5 is proved without HS_proof: the pinch transport
  (`HilbertSmith.Interface.pinchTransport`); what §6 uses of Proposition 5.1, without its
  orientation step (which stays the input `Orientation.exists_restrict`), from
  `HilbertSmith.NewmanInput` and without second countability
  (`HilbertSmith.Interface.chartReductionNoSC`); Lemma 5.2 (`HilbertSmith.Interface.collapseInput`);
  what §6 uses of Lemma 5.6, the region `V` and its multiplier `β`
  (`HilbertSmith.Interface.sheetsInput`); Lemma 5.7 (Deicyde's `HilbertSmith.homotopyExtension`);
  and, from §6, the neighbourhood bases of `S^d` and `C_d` (`HilbertSmith.Interface.sphereBasis`,
  `HilbertSmith.Interface.closePairBasis`). Newman's theorem is a hypothesis of `oai_route`;
  `oai_route_noSC` discharges it from HS_proof (`HSBridge.newmanInput`), as HS_proof's own route
  does (`HSFormal.Newman.newmanPrimeOrder`). Definition 6.3, Propositions 5.8, 6.4–6.7 and Theorem
  6.8 are proved from the interface.

In this build, any statement whose hypotheses include a faithful action of `ℤ_[p]` on a manifold
can be discharged ex falso from HS_proof: from `HSBridge.hs_route_univ` when the manifold is second
countable, and from `HSGeneral.padicExclusionNoSC` otherwise. That is why the audit below matters:
`oai_route` passes `#assert_route_pure`, and `oai_route_noSC`, which uses `HSBridge.newmanInput`,
passes `#assert_route_pure … allowing HSBridge.newmanInput`: everything it reaches in HS_proof is
reached through Newman's theorem. A guarded check also shows that `HSBridge.newmanInput` itself
reaches neither HS_proof's L-theory nor its p-adic exclusion theorems.

The interface's weakest point of non-vacuity is `OAIInvariant.isTest_closePair`: a model needs a
triangulation of the close-pair test `C_d` (semialgebraic, or Whitehead's for a smooth manifold
with boundary), or another proof of Proposition 6.6. The cross-polytope variant of the close-pair
test (plan item B-P, on `isTest_closePair`) would avoid it; that choice is made before the sheaf
model of §§2–4 is built.

So this file compares proof architectures modulo interfaces, not two complete proofs.

## The purity audit

`HSFormal.padicExclusion` proves every statement of the form "hypotheses imply p-adic exclusion",
so `oai_route` means something only because its proof does not use HS_proof. The commands at the
end of this file check that in the build and print the reports in the build log:

* `oai_route` reaches no constant of HS_proof, and `oai_route_noSC` none except through
  `HSBridge.newmanInput`, which avoids `HSFormal.LTheory`, `HSFormal.padicExclusion` and
  `HSFormal.Universe.padicExclusion_univ` (all guarded by `#guard_msgs`);
* `hs_route`'s proof reaches HS_proof's L-theory (`HSFormal.LTheory.*`), checked from its value;
* `hs_route_of_inputs` mentions `HSFormal.LTheory.*` already in its signature (its hypothesis
  `𝕃 : HSFormal.LTheory.LowerLTheory`, and the type of `HSFormal.padicExclusion_of_inputs`), so
  that check is signature-level;
* the interface fields `oai_route` assumes, generated from the structures `OAIInterface` and
  `LocalInputs`, and its other hypothesis `NewmanInput` (guarded, so adding or removing a field
  fails the build), and the same list for `oai_route_noSC`, which has no `NewmanInput` (guarded);
* D1's module table (plan item D1, §5.2): the HS_proof modules each HS_proof theorem reaches, split
  into the shared front (the import closure, inside HS_proof, of the modules whose declarations
  OpenAI's front would reuse: 46 modules at the pinned HS_proof) and the back end.

## The two interfaces, kind by kind

`HSBridge.interfaceComparison` is B1's table (plan item B1, §4). Every non-empty cell is a list of
declaration names, checked when this file is compiled, so the table cannot cite a declaration that
does not exist; two cells are empty, as in B1.
-/

namespace HSBridge

universe u

/-- **HS_proof's route, unconditional**: p-adic exclusion for second-countable manifolds in `Type`,
by HS_proof's `HSFormal.padicExclusion`. -/
theorem hs_route : HilbertSmith.Statements.PadicExclusion.{0} :=
  statements_agree.2 HSFormal.padicExclusion

/-- HS_proof's route in every universe, by `HSFormal.Universe.padicExclusion_univ`. -/
theorem hs_route_univ : HilbertSmith.Statements.PadicExclusion.{u} :=
  statements_agree_univ.2 HSFormal.Universe.padicExclusion_univ

/-- **HS_proof's route at its interface level** (`HSFormal.padicExclusion_of_inputs`): from an
L-theory `𝕃 : HSFormal.LTheory.LowerLTheory` and Newman's theorem for prime order. -/
theorem hs_route_of_inputs (𝕃 : HSFormal.LTheory.LowerLTheory) (hN : HSFormal.NewmanPrimeOrder) :
    HilbertSmith.Statements.PadicExclusion.{0} :=
  statements_agree.2 (HSFormal.padicExclusion_of_inputs 𝕃 hN)

/-- **OpenAI's route at its interface level**
(`HilbertSmith.Interface.padicExclusion_of_oaiInterface`): from OpenAI's interface, the local
inputs of §5 and Newman's theorem, the same conclusion as `hs_route`. -/
theorem oai_route (O : HilbertSmith.Interface.OAIInterface)
    (T : HilbertSmith.Interface.LocalInputs O) (hN : HilbertSmith.NewmanInput.{u}) :
    HilbertSmith.Statements.PadicExclusion.{u} :=
  HilbertSmith.Interface.padicExclusion_of_oaiInterface O T hN

/-- **OpenAI's route without second countability**
(`HilbertSmith.Interface.padicExclusion_of_oaiInterface_noSC`): from OpenAI's interface and the
local inputs of §5, with Newman's theorem discharged from HS_proof by `HSBridge.newmanInput`. -/
theorem oai_route_noSC (O : HilbertSmith.Interface.OAIInterface)
    (T : HilbertSmith.Interface.LocalInputs O) : HilbertSmith.Statements.PadicExclusionNoSC.{u} :=
  HilbertSmith.Interface.padicExclusion_of_oaiInterface_noSC O T newmanInput

/-- A row of the comparison of the two interfaces: a kind of property, the declarations that
supply it on each side (empty if none), and how the two differ. -/
structure ComparisonRow where
  /-- The kind of property. -/
  kind : String
  /-- HS_proof's declarations. -/
  hs : List Lean.Name
  /-- OpenAI's route's declarations. -/
  oai : List Lean.Name
  /-- How they differ. -/
  note : String

/-- **The two interfaces, kind by kind** (plan item B1, §4). Every non-empty cell is a list of
checked name literals. -/
def interfaceComparison : List ComparisonRow := [
  ⟨"The group",
    [``HSFormal.LTheory.LowerLTheory.L],
    [``HilbertSmith.Interface.OAIInvariant.E, ``HilbertSmith.Interface.OAIInvariant.WQ],
    "a Witt/L-type group; HS_proof algebraic and in every degree, \
      OpenAI geometric and in degree d"⟩,
  ⟨"Functoriality",
    [``HSFormal.LTheory.LowerLTheory.map, ``HSFormal.LTheory.LowerLTheory.map_id,
      ``HSFormal.LTheory.LowerLTheory.map_comp],
    [``HilbertSmith.Interface.OAIInvariant.map, ``HilbertSmith.Interface.OAIInvariant.map_id,
      ``HilbertSmith.Interface.OAIInvariant.map_comp, ``HilbertSmith.Interface.OAIInvariant.pushQ,
      ``HilbertSmith.Interface.OAIInvariant.wmap_cls],
    "along functors of categories with involution vs along continuous maps of test spaces"⟩,
  ⟨"Isometry invariance",
    [``HSFormal.LTheory.LowerLTheory.map_unitaryIso],
    [``HilbertSmith.Interface.WittClasses.cls_isometry],
    "unitarily isomorphic functors vs isometric forms"⟩,
  ⟨"Additivity",
    [``HSFormal.LTheory.LowerLTheory.map_finSum],
    [``HilbertSmith.Interface.WittClasses.cls_orthSum,
      ``HilbertSmith.Interface.WittClasses.cls_neg],
    "OpenAI also needs negation, for the involution of Proposition 6.4"⟩,
  ⟨"Forms to classes",
    [``HSFormal.LTheory.LowerLTheory.cls, ``HSFormal.LTheory.LowerLTheory.cls_map],
    [``HilbertSmith.Interface.WittClasses.cls,
      ``HilbertSmith.Interface.OrbitCharacterTheory.form_cls],
    "HS_proof passes between decorations; OpenAI's test categories are closed under summands"⟩,
  ⟨"Localization",
    [``HSFormal.LTheory.LowerLTheory.bdry, ``HSFormal.LTheory.LowerLTheory.exact_A,
      ``HSFormal.LTheory.LowerLTheory.exact_Q, ``HSFormal.LTheory.LowerLTheory.exact_U,
      ``HSFormal.LTheory.LowerLTheory.bdry_natural],
    [``HilbertSmith.Interface.OAIInvariant.ℓ, ``HilbertSmith.Interface.OAIInvariant.ℓ_natural],
    "HS_proof uses the boundary map; \
      OpenAI's §6 only the case where the sequence is an isomorphism"⟩,
  ⟨"Pair boundary and its sign",
    [``HSFormal.LTheory.LowerLTheory.bsign, ``HSFormal.LTheory.LowerLTheory.bdry_pair],
    [],
    "OpenAI's §6 computes no boundary"⟩,
  ⟨"Integrality",
    [``HSFormal.LTheory.LowerLTheory.dec_bij],
    [``HilbertSmith.Interface.OAIInvariant.lattice, ``HilbertSmith.Interface.OAIInvariant.L_pos,
      ``HilbertSmith.Interface.OAIInvariant.u_nontorsion],
    "an integral constraint fixed in advance: \
      exact integers vs a bounded power-of-two denominator"⟩,
  ⟨"Idempotents",
    [``HSFormal.LTheory.BS01, ``HSFormal.LTheory.bs01],
    [``HilbertSmith.Interface.Form.twist],
    "HS_proof splits idempotents; OpenAI twists by 2e - 1 instead (Definition 6.3)"⟩,
  ⟨"Homotopy invariance",
    [``HSFormal.GermHomotopyInvariance, ``HSFormal.germHomotopyInvariance],
    [``HilbertSmith.Interface.OAIInvariant.map_homotopic,
      ``HilbertSmith.Interface.OrbitCharacterTheory.z_homotopic],
    "proved for one germ in HS_proof; an interface field for all maps in OpenAI's"⟩,
  ⟨"Normalization",
    [``HSFormal.PinchSignature, ``HSFormal.pinchSignature],
    [``HilbertSmith.Interface.OrbitCharacterTheory.form_cls,
      ``HilbertSmith.Interface.OAIInvariant.mapD],
    "a signature after iterated boundaries vs a rational sphere class"⟩,
  ⟨"Reading a number",
    [``HSFormal.FibreSignature],
    [``HilbertSmith.Interface.OAIInvariant.lattice],
    "an integer tail of a signature vs the coefficient of u_d, implicit in the lattice"⟩,
  ⟨"Characters",
    [``HSFormal.ControlData.SheetData, ``HSFormal.SignatureDecomposition.prime_dvd_signature],
    [``HilbertSmith.Interface.OrbitCharacterTheory.proj,
      ``HilbertSmith.Interface.OrbitCharacterTheory.proj_mul,
      ``HilbertSmith.Interface.OrbitCharacterTheory.proj_sum,
      ``HilbertSmith.Interface.OrbitCharacterTheory.proj_adj],
    "proved on the algebra side in HS_proof: SheetData is the hypotheses of (★), the divisibility \
      of the fibre tail signature by p, and SignatureDecomposition.prime_dvd_signature is the \
      cyclotomic Lemma 3.1; sheaf fields (Lemmas 6.1, 6.2) in OpenAI's"⟩,
  ⟨"Covariance of the pieces",
    [``HSFormal.LTheory.SupportHom.cutBdry_natural],
    [``HilbertSmith.Interface.OrbitCharacterTheory.push,
      ``HilbertSmith.Interface.OrbitCharacterTheory.map_z],
    "a theorem in HS_proof; a field, then Proposition 6.5, in OpenAI's"⟩,
  ⟨"Sheet twist",
    [``HSFormal.AsymptoticCategory.exists_unitary_localTriv],
    [``HilbertSmith.Interface.OrbitCharacterTheory.twist,
      ``HilbertSmith.Interface.SheetMultiplier],
    "order p on a finite cover vs order p^k on one region, which forces the move test"⟩,
  ⟨"Excision",
    [``HSFormal.LTheory.isUnitaryEquiv_excision],
    [],
    "OpenAI's excision lives in §3, behind the lattice"⟩,
  ⟨"Contradiction",
    [``HSFormal.notMem_divTail_of_isSignTail],
    [``HilbertSmith.Interface.OrbitCharacterTheory.false_of_test],
    "1 is not in pZ vs m does not divide 4 L_d for m = p^k > 4 L_d"⟩,
  ⟨"Topological inputs",
    [``HSFormal.NewmanPrimeOrder, ``HSFormal.exists_chartData],
    [``HilbertSmith.Interface.LocalInputs, ``HilbertSmith.Interface.chartReductionNoSC,
      ``HilbertSmith.NewmanInput],
    "overlap on Newman and the chart; OpenAI adds Čech cohomology and Serre's theorem"⟩,
  ⟨"Second countability",
    [``HSFormal.PadicExclusion, ``HSGeneral.padicExclusionNoSC],
    [``HilbertSmith.Interface.chartReductionNoSC,
      ``HilbertSmith.Interface.padicExclusion_of_oaiInterface_noSC],
    "HS_proof's Lean theorem assumes it and the HS paper removes it by a global invariant \
      exhaustion (formalized unconditionally in HSGeneral); OpenAI's Proposition 5.1 never \
      leaves one chart, so its route concludes the statement without it, from its interfaces"⟩
]

/-! ### The audit, printed in the build log -/

/-- info: route audit: 'HSBridge.oai_route' depends on no constant from HS_proof -/
#guard_msgs in
#assert_route_pure oai_route

#route_report oai_route

/--
info: route audit: 'HSBridge.oai_route_noSC' depends on no constant from HS_proof except through:
  HSBridge.newmanInput
-/
#guard_msgs (whitespace := lax) in
#assert_route_pure oai_route_noSC allowing HSBridge.newmanInput

#route_report oai_route_noSC

-- The discharge of Newman's theorem stays away from HS_proof's L-theory and from its p-adic
-- exclusion theorems.

/--
info: route audit: 'HSBridge.newmanInput' avoids modules under HSFormal.LTheory and the constants
  HSFormal.padicExclusion, HSFormal.Universe.padicExclusion_univ
-/
#guard_msgs (whitespace := lax) in
#assert_route_avoids HSBridge.newmanInput modules [HSFormal.LTheory]
  constants [HSFormal.padicExclusion, HSFormal.Universe.padicExclusion_univ]

-- `oai_route_noSC` takes the same structures as `oai_route` (expanded below), and no `NewmanInput`.
/--
info: route assumptions of 'HSBridge.oai_route_noSC':
O : HilbertSmith.Interface.OAIInterface
  δD
  OP
  inv
  chars
T : HilbertSmith.Interface.LocalInputs O
  orientation
  averagedTest
  orbitNull
-/
#guard_msgs (whitespace := lax) in
#route_assumptions oai_route_noSC

/--
info: route audit: the value of 'HSBridge.hs_route' depends on constants from modules under
  'HSFormal.LTheory'
-/
#guard_msgs (whitespace := lax) in
#assert_route_reaches_by_value hs_route HSFormal.LTheory

#route_report hs_route

-- Signature-level: `hs_route_of_inputs` takes `𝕃 : HSFormal.LTheory.LowerLTheory`.
/--
info: route audit: 'HSBridge.hs_route_of_inputs' depends on constants from modules under
  'HSFormal.LTheory'
-/
#guard_msgs (whitespace := lax) in
#assert_route_reaches hs_route_of_inputs HSFormal.LTheory

#route_report hs_route_of_inputs

/-! ### The interface fields `oai_route` assumes -/

/--
info: route assumptions of 'HSBridge.oai_route':
O : HilbertSmith.Interface.OAIInterface
  δD
  OP
  inv (HilbertSmith.Interface.OAIInvariant, expanded)
    IsTest
    isTest_sphere
    isTest_closePair
    E
    grp
    map
    map_id
    map_comp
    map_homotopic
    u
    L
    L_pos
    lattice
    u_nontorsion
    mapD
    Q
    cat
    preadd
    biprod
    dual (HilbertSmith.Duality, expanded)
      D
      biduality
    dualAdd
    WQ
    wgrp
    witt (HilbertSmith.Interface.WittClasses, expanded)
      cls
      cls_isometry
      cls_orthSum
      cls_neg
    ℓ
    pushQ (HilbertSmith.Interface.DualFunctor, expanded)
      F
      additive
      η
      bidual
    wmap
    wmap_cls
    ℓ_natural
  chars (HilbertSmith.Interface.OrbitCharacterTheory, expanded)
    form
    form_cls
    proj
    proj_mul
    proj_sum
    proj_adj
    push
    twist
T : HilbertSmith.Interface.LocalInputs O
  orientation (HilbertSmith.Interface.Orientation, expanded)
    exists_restrict
    restrict
    stabilize
  averagedTest
  orbitNull
hN : HilbertSmith.NewmanInput (not a structure)
-/
#guard_msgs (whitespace := lax) in
#route_assumptions oai_route
  expanding HilbertSmith.Interface.OAIInvariant HilbertSmith.Interface.OrbitCharacterTheory
    HilbertSmith.Interface.Orientation HilbertSmith.Interface.WittClasses
    HilbertSmith.Interface.DualFunctor HilbertSmith.Duality

/-! ### D1's module table: HS_proof's shared front against its back end

The front is the import closure, inside HS_proof, of the eleven modules whose declarations
OpenAI's front would reuse (plan item D1, §5.2). Unguarded: the lists depend on the HS_proof pin;
the stable fact, that `hs_route` reaches `HSFormal.LTheory`, is guarded above. -/

#route_modules hs_route front HSFormal.WeakInputs HSFormal.Reduction HSFormal.MontgomeryPrime
  HSFormal.PadicSubgroups HSFormal.PadicStabilizers HSFormal.FreePoint HSFormal.FixedData
  HSFormal.Newman.Newman HSFormal.Newman.Degree HSFormal.Inputs.GY.NSSIsLie HSFormal.Inputs.Lemma7

#route_modules hs_route_of_inputs front HSFormal.WeakInputs HSFormal.Reduction
  HSFormal.MontgomeryPrime HSFormal.PadicSubgroups HSFormal.PadicStabilizers HSFormal.FreePoint
  HSFormal.FixedData HSFormal.Newman.Newman HSFormal.Newman.Degree HSFormal.Inputs.GY.NSSIsLie
  HSFormal.Inputs.Lemma7

end HSBridge
