import HSBridge.Purity
import HSBridge.Statements
import HSFormal.HilbertSmith
import HSFormal.HilbertSmithModel
import HilbertSmith.Interface.Main

/-!
# The two routes side by side

Both routes prove p-adic exclusion for second-countable manifolds, the statement
`HilbertSmith.Statements.PadicExclusion` (OpenAI's Theorem 1.2).

* `HSBridge.statements_agree` (in `HSBridge.Statements`): it is HS_proof's
  `HSFormal.PadicExclusion`, by `Iff.rfl`.
* `HSBridge.hs_route`: HS_proof's proof, unconditional, and `HSBridge.hs_route_univ` in every
  universe.
* `HSBridge.hs_route_of_inputs`: HS_proof's proof at its interface level,
  `HSFormal.padicExclusion_of_inputs`: from its L-theory interface `HSFormal.LTheory.LowerLTheory`
  and Newman's theorem `HSFormal.NewmanPrimeOrder`.
* `HSBridge.oai_route`: OpenAI's proof at its interface level,
  `HilbertSmith.Interface.padicExclusion_of_oaiInterface`: from `OAIInterface` (the Witt groups of
  sheaves, as §§5–6 use them) and `LocalInputs` (the topology of §5).

## What each route assumes

The same conclusion with two sets of hypotheses, and an asymmetry:

* HS_proof discharges both of its hypotheses: `LowerLTheory` by its model
  `HSFormal.LTheory.lowerLModel` (used in `HSFormal.padicExclusion_of_model`), and Newman's
  theorem by `HSFormal.Newman.newmanPrimeOrder`.
* OpenAI's route discharges neither yet. `OAIInterface` needs the sheaf model of §§2–4 (B-M7).
  `LocalInputs` collects, from §5: Proposition 5.1 without orientation (`ChartReduction`, assumed;
  stated with second countability as in OpenAI's standing hypotheses; B-M3 is to prove it, and a
  form without second countability, from `HilbertSmith.NewmanInput`, which `HSBridge.newmanInput`
  discharges from HS_proof), the orientation facts, Lemma 5.2 (`CollapseInput`), Lemma 5.3 with
  the pinch transport (`AveragedTest`), Lemmas 5.4 and 5.5 combined (`OrbitNull`), Lemma 5.6
  (`SheetsInput`) and the neighbourhood bases of `S^d` and `C_d`. Lemma 5.7 is proved (Deicyde's
  `HilbertSmith.homotopyExtension`), as are Definition 6.3, Propositions 5.8, 6.4–6.7 and
  Theorem 6.8 from the interface.

So this file compares proof architectures modulo interfaces, not two complete proofs.

## The purity audit

`HSFormal.padicExclusion` proves every statement of the form "hypotheses imply p-adic exclusion",
so `oai_route` means something only because its proof does not use HS_proof. The commands at the
end of this file check that in the build and print the reports in the build log: `oai_route`
reaches no constant of `HSFormal`, while `hs_route` and `hs_route_of_inputs` reach HS_proof's
L-theory (`HSFormal.LTheory.*`).

## The two interfaces, kind by kind

`HSBridge.interfaceComparison` is B1's table (plan item B1, §4) with a declaration name in every
cell; the names are checked when this file is compiled, so the table cannot cite a declaration
that does not exist.
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
(`HilbertSmith.Interface.padicExclusion_of_oaiInterface`): from OpenAI's interface and the local
inputs of §5, the same conclusion as `hs_route`. -/
theorem oai_route (O : HilbertSmith.Interface.OAIInterface)
    (T : HilbertSmith.Interface.LocalInputs.{u} O) : HilbertSmith.Statements.PadicExclusion.{u} :=
  HilbertSmith.Interface.padicExclusion_of_oaiInterface O T

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

/-- **The two interfaces, kind by kind** (plan item B1, §4). Every name is a checked literal. -/
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
  ⟨"Characters",
    [``HSFormal.ControlData.SheetData],
    [``HilbertSmith.Interface.OrbitCharacterTheory.proj,
      ``HilbertSmith.Interface.OrbitCharacterTheory.proj_mul,
      ``HilbertSmith.Interface.OrbitCharacterTheory.proj_sum,
      ``HilbertSmith.Interface.OrbitCharacterTheory.proj_adj],
    "proved on the algebra side in HS_proof; sheaf fields (Lemmas 6.1, 6.2) in OpenAI's"⟩,
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
    [``HSFormal.NewmanPrimeOrder],
    [``HilbertSmith.Interface.LocalInputs, ``HilbertSmith.NewmanInput],
    "overlap on Newman and the chart; OpenAI adds Čech cohomology and Serre's theorem"⟩
]

/-! ### The audit, printed in the build log -/

/-- info: route audit: 'HSBridge.oai_route' depends on no constant from HSFormal -/
#guard_msgs in
#assert_route_pure oai_route

#route_report oai_route

#assert_route_reaches hs_route HSFormal.LTheory

#route_report hs_route

#assert_route_reaches hs_route_of_inputs HSFormal.LTheory

#route_report hs_route_of_inputs

end HSBridge
