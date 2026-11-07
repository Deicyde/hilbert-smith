import HSBridge.PurityFixtures.Clean
import HilbertSmith
import HSBridge.Purity
import HSBridge.PurityFixtures.Tainted
import HSBridge.PurityFixtures.TwinHS
import HSBridge.PurityFixtures.TwinClean
import HSBridge.Statements
import HSFormal.Universe
import FCChallenge
import FCSolution

/-!
# Tests for the route-separation audit

These tests are part of the build: each `#guard_msgs` fails the build if the audit's verdict
changes. They show that `#assert_route_pure`

* catches a theorem that uses HS_proof's `HSFormal.padicExclusion`, directly, through our own
  declarations, or as an ex-falso interface field, and a constant of an HS_proof module outside
  the `HSFormal` namespace;
* catches a theorem of HS_proof's library `FCSolution` whose name Lean attributes to
  `FCChallenge`, and refuses to decide when a name is held by an HS_proof module and by another;
* walks every copy of a name held by several modules of the same kind, not only the kernel's;
* passes honest theorems, including one from a module that imports HS_proof;
* refuses allow-lists that name an HS_proof constant, a constant that is not a declared discharge,
  or a constant the theorem does not reach.

The last tests check the import boundary: no module of the library `HilbertSmith` imports
HS_proof. Messages are guarded without counts, so that a new HS_proof pin does not break them.

The declarations here are planted for the tests and are used nowhere else.
-/

namespace HSBridge.PurityTest

/-! ### Planted violations -/

/-- **Planted violation.** Any "interface implies p-adic exclusion" statement can be proved from
HS_proof's unconditional theorem, ignoring the interface (PLAN risk 1). The audit must catch it. -/
theorem planted (_interface : Prop) (_h : _interface) :
    HilbertSmith.Statements.PadicExclusion.{0} :=
  HSBridge.statements_agree.2 HSFormal.padicExclusion

/-- The planted violation, laundered through a declaration of our own. -/
theorem laundered : HilbertSmith.Statements.PadicExclusion.{0} :=
  planted True trivial

/-- An interface field "no faithful action" discharged ex falso from HS_proof, in a structure of
our own (PLAN risk 1). -/
structure FakeInterface : Prop where
  /-- A field that HS_proof's theorem proves outright. -/
  noFaithful : HilbertSmith.Statements.PadicExclusion.{0}

/-- The fake interface, discharged by HS_proof. -/
theorem fakeInterface : FakeInterface :=
  ⟨HSBridge.statements_agree.2 HSFormal.padicExclusion⟩

/-- A use of a constant that lies outside the `HSFormal` namespace but belongs to an HS_proof
module: the congruence lemma of Mathlib's `Homeomorph.smulOfNeZero`, which Lean realized inside
`HSFormal.ChartData`. The audit attributes constants by module, so it reports this (harmless) use:
it errs on the safe side. -/
theorem outsideNamespace (c d : ℝ) (h : c = d) (hc : c ≠ 0) :
    Homeomorph.smulOfNeZero (α := ℝ) c hc = Homeomorph.smulOfNeZero d (h ▸ hc) :=
  Homeomorph.smulOfNeZero.congr_simp c d h hc

/-- A use of `Homeomorph.addRight.congr_simp`, of which the build holds two copies: one realized in
`HSBridge.PurityFixtures.Clean` (imported first, so Lean's index names that module) and one in
`HSFormal.ChartData`. -/
theorem twoCopies (x y : ℝ) (h : x = y) : Homeomorph.addRight x = Homeomorph.addRight y :=
  Homeomorph.addRight.congr_simp x y h

/-- A theorem using both an allowed constant and HS_proof's theorem. -/
theorem plantedWithNewman :
    HilbertSmith.NewmanInput.{0} ∧ HilbertSmith.Statements.PadicExclusion.{0} :=
  ⟨HSBridge.newmanInput, planted True trivial⟩

/-! ### Honest declarations -/

/-- An honest theorem of the right shape: its hypothesis is used. -/
theorem honest (h : HilbertSmith.Statements.PadicExclusion.{0}) :
    HilbertSmith.Statements.PadicExclusion.{0} :=
  h

/-- Newman's theorem in OpenAI's form, used through the bridge's discharge. -/
theorem usesNewman : HilbertSmith.NewmanInput.{0} :=
  HSBridge.newmanInput

/-- A theorem whose hypothesis is HS_proof's statement, used only to test
`#assert_route_reaches_by_value`. -/
theorem viaHypothesis (h : HSFormal.PadicExclusion) : HilbertSmith.Statements.PadicExclusion.{0} :=
  h

/-- A theorem using `HSBridge.PurityFixtures.twin`, a name with two copies of the same kind. -/
theorem usesTwin : 3 + 0 = 3 :=
  HSBridge.PurityFixtures.twin 3

/-- A theorem using a clean constant of a module that imports HS_proof. -/
theorem usesTaintedModule (n : ℕ) : 2 * n = n + n :=
  HSBridge.PurityFixtures.two_mul_eq_add n

/-! ### The audit's verdicts -/

-- Planted violations are caught: directly, through a declaration of our own, as an ex-falso
-- interface field, and next to an allowed constant.

/--
error: route audit: 'HSBridge.PurityTest.planted' depends on HS_proof; entry points:
  HSFormal.PadicExclusion
  HSFormal.padicExclusion
-/
#guard_msgs (whitespace := lax) in
#assert_route_pure planted

/--
error: route audit: 'HSBridge.PurityTest.laundered' depends on HS_proof; entry points:
  HSFormal.PadicExclusion
  HSFormal.padicExclusion
-/
#guard_msgs (whitespace := lax) in
#assert_route_pure laundered

/--
error: route audit: 'HSBridge.PurityTest.fakeInterface' depends on HS_proof; entry points:
  HSFormal.PadicExclusion
  HSFormal.padicExclusion
-/
#guard_msgs (whitespace := lax) in
#assert_route_pure fakeInterface

/--
error: route audit: 'HSBridge.PurityTest.plantedWithNewman' depends on HS_proof; entry points:
  HSFormal.PadicExclusion
  HSFormal.padicExclusion
-/
#guard_msgs (whitespace := lax) in
#assert_route_pure plantedWithNewman allowing HSBridge.newmanInput

/--
error: route audit: 'HSFormal.padicExclusion' depends on HS_proof; entry points:
  HSFormal.padicExclusion
-/
#guard_msgs (whitespace := lax) in
#assert_route_pure HSFormal.padicExclusion

-- Constants are attributed by module, so a constant outside the `HSFormal` namespace is caught.

/--
error: route audit: 'HSBridge.PurityTest.outsideNamespace' depends on HS_proof; entry points:
  Homeomorph.smulOfNeZero.congr_simp
-/
#guard_msgs (whitespace := lax) in
#assert_route_pure outsideNamespace

/-! ### Names held by several modules

`FCChallenge` (statement, proof `sorry`, imports only Mathlib) and `FCSolution` (the same statement,
proved from HS_proof) both declare
`Hilbert5.hilbert_smith_padic_formulation.variants.second_countable`. Lean accepts importing both,
in either order. With `FCChallenge` imported first, as here, Lean's index of declaring modules names
`FCChallenge`, while the kernel holds `FCSolution`'s body, which uses
`HSFormal.Universe.padicExclusion_univ`. An audit that trusted the index and counted only modules
under `HSFormal` as HS_proof would not enter the constant (`FCChallenge` imports no HS_proof module)
and would pass it. In the other order Lean's index names `FCSolution` and the kernel holds
`FCChallenge`'s `sorry` body, so such an audit would again pass it, while `#print axioms`, which
reads the axioms recorded for `FCSolution`'s copy, would report no `sorryAx`: the statement would
look proved without HS_proof. Both modules belong to HS_proof's package, so the audit catches the
constant in either order; `HSBridge.PurityFixtures.FCReversed` tests the other order.

No theorem of ours is built on it here: `#print axioms` reads the axioms recorded for the module
Lean's index names, so it would report `sorryAx` for such a theorem although the kernel holds the
proof from HS_proof. The audit is run on the constant itself.

Building `FCChallenge` makes Lake print two `declaration uses 'sorry'` warnings. They come from
HS_proof's own `FCChallenge.lean`, whose proofs are `sorry` by design (it is a challenge file for
comparator), and are outside our package; this test needs that file in the build. -/

/--
error: route audit: 'Hilbert5.hilbert_smith_padic_formulation.variants.second_countable' depends
  on HS_proof; entry points:
  Hilbert5.hilbert_smith_padic_formulation.variants.second_countable
-/
#guard_msgs (whitespace := lax) in
#assert_route_pure Hilbert5.hilbert_smith_padic_formulation.variants.second_countable

-- A name held by an HS_proof module and a module free of HS_proof: the audit refuses to decide.

/--
error: route audit: 'HSBridge.PurityTest.twoCopies' depends on constants of ambiguous provenance,
  declared by modules of different kinds:
  Homeomorph.addRight.congr_simp
-/
#guard_msgs (whitespace := lax) in
#assert_route_pure twoCopies

-- A name held by two modules of the same kind (both import HS_proof, neither belongs to it): the
-- audit walks both copies. The kernel keeps `TwinClean`'s copy, which uses nothing from HS_proof;
-- `TwinHS`'s copy mentions `HSFormal.PadicExclusion`, and the audit finds it.

/--
error: route audit: 'HSBridge.PurityFixtures.twin' depends on HS_proof; entry points:
  HSFormal.PadicExclusion
-/
#guard_msgs (whitespace := lax) in
#assert_route_pure HSBridge.PurityFixtures.twin

/--
error: route audit: 'HSBridge.PurityTest.usesTwin' depends on HS_proof; entry points:
  HSFormal.PadicExclusion
-/
#guard_msgs (whitespace := lax) in
#assert_route_pure usesTwin

-- Honest declarations pass: our own, a theorem of OpenAI's route, the compared statement, and a
-- clean constant of a module that imports HS_proof, used directly and through our own theorem.

/-- info: route audit: 'HSBridge.PurityTest.honest' depends on no constant from HS_proof -/
#guard_msgs (whitespace := lax) in
#assert_route_pure honest

/-- info: route audit: 'HilbertSmith.closed_eq_dvd_pow' depends on no constant from HS_proof -/
#guard_msgs (whitespace := lax) in
#assert_route_pure HilbertSmith.closed_eq_dvd_pow

/--
info: route audit: 'HilbertSmith.Statements.PadicExclusion' depends on no constant from HS_proof
-/
#guard_msgs (whitespace := lax) in
#assert_route_pure HilbertSmith.Statements.PadicExclusion

/--
info: route audit: 'HSBridge.PurityFixtures.two_mul_eq_add' depends on no constant from HS_proof
-/
#guard_msgs (whitespace := lax) in
#assert_route_pure HSBridge.PurityFixtures.two_mul_eq_add

/--
info: route audit: 'HSBridge.PurityTest.usesTaintedModule' depends on no constant from HS_proof
-/
#guard_msgs (whitespace := lax) in
#assert_route_pure usesTaintedModule

-- The allow-list admits exactly the paths through the declared discharges; it refuses an HS_proof
-- constant, a constant that is not a declared discharge, and a stale entry.

/--
error: route audit: 'HSBridge.PurityTest.usesNewman' depends on HS_proof; entry points:
  HSFormal.newman_rigidity'
  HSFormal.Newman.newmanPrimeOrder
-/
#guard_msgs (whitespace := lax) in
#assert_route_pure usesNewman

/--
info: route audit: 'HSBridge.PurityTest.usesNewman' depends on no constant from HS_proof
  except through:
  HSBridge.newmanInput
-/
#guard_msgs (whitespace := lax) in
#assert_route_pure usesNewman allowing HSBridge.newmanInput

/--
error: route audit: an allow-list may not name constants of HS_proof:
  HSFormal.padicExclusion
-/
#guard_msgs (whitespace := lax) in
#assert_route_pure planted allowing HSFormal.padicExclusion

/--
error: route audit: not declared discharges (HSBridge.Purity.declaredDischarges):
  HSBridge.PurityTest.planted
-/
#guard_msgs (whitespace := lax) in
#assert_route_pure laundered allowing planted

/--
error: route audit: 'HSBridge.PurityTest.planted' does not depend on the allowed constants:
  HSBridge.newmanInput
-/
#guard_msgs (whitespace := lax) in
#assert_route_pure planted allowing HSBridge.newmanInput

-- The report counts what a declaration reaches inside HS_proof, by module (unguarded: the counts
-- depend on the HS_proof pin).

/-- info: route audit: 'HSBridge.PurityTest.honest' depends on no constant from HS_proof -/
#guard_msgs (whitespace := lax) in
#route_report honest

#route_report usesNewman

-- The positive check: the planted theorem goes through HS_proof's L-theory; Newman does not.

/--
info: route audit: 'HSBridge.PurityTest.planted' depends on constants from modules under
  'HSFormal.LTheory'
-/
#guard_msgs (whitespace := lax) in
#assert_route_reaches planted HSFormal.LTheory

/--
info: route audit: the value of 'HSBridge.PurityTest.planted' depends on constants from modules
  under 'HSFormal.LTheory'
-/
#guard_msgs (whitespace := lax) in
#assert_route_reaches_by_value planted HSFormal.LTheory

/--
error: route audit: 'HSBridge.PurityTest.usesNewman' depends on no constant from modules under
  'HSFormal.LTheory'
-/
#guard_msgs (whitespace := lax) in
#assert_route_reaches usesNewman HSFormal.LTheory

-- `viaHypothesis` mentions `HSFormal.PadicExclusion` only in its hypothesis: the type-level check
-- sees it, the value-level check does not.

/--
info: route audit: 'HSBridge.PurityTest.viaHypothesis' depends on constants from modules under
  'HSFormal'
-/
#guard_msgs (whitespace := lax) in
#assert_route_reaches viaHypothesis HSFormal

/--
error: route audit: the value of 'HSBridge.PurityTest.viaHypothesis' depends on no constant from
  modules under 'HSFormal'
-/
#guard_msgs (whitespace := lax) in
#assert_route_reaches_by_value viaHypothesis HSFormal

-- The listing of assumptions: nested structures in `expanding` are expanded, flags apply at any
-- depth, a hypothesis that is not a structure is printed as such, and an unmatched flag fails.

/-- Two laws, for the test of `#route_assumptions`. -/
structure InnerLaws : Prop where
  /-- A law. -/
  first : True
  /-- Another law. -/
  second : 1 = 1

/-- A structure with a nested one, for the test of `#route_assumptions`. -/
structure OuterLaws : Prop where
  /-- The nested laws, for every `n`. -/
  inner : ∀ n : ℕ, n = n → InnerLaws
  /-- A law of its own. -/
  third : True

/-- A theorem with a structure hypothesis and one that is not. -/
theorem withLaws (n : ℕ) (_h : OuterLaws) : n = n :=
  rfl

/--
info: route assumptions of 'HSBridge.PurityTest.withLaws':
n : ℕ (not a structure)
_h : OuterLaws
  inner (HSBridge.PurityTest.InnerLaws, expanded)
    first
    second
      flagged: a nested flag
  third
-/
#guard_msgs (whitespace := lax) in
#route_assumptions withLaws flag second "a nested flag" expanding InnerLaws

/--
error: route assumptions: flags that match no listed field:
  fourth
-/
#guard_msgs (whitespace := lax) in
#route_assumptions withLaws flag fourth "no such field" expanding InnerLaws

-- `#assert_route_avoids`: the planted theorem reaches HS_proof's L-theory, its Newman theorem and
-- its p-adic exclusion theorem; the bridge's discharge of Newman's theorem reaches neither the
-- L-theory nor the p-adic exclusion theorem.

/--
error: route audit: 'HSBridge.PurityTest.planted' reaches constants of modules under
  HSFormal.LTheory, HSFormal.Newman and the constants HSFormal.padicExclusion,
  HSFormal.newman_rigidity'
-/
#guard_msgs (whitespace := lax) in
#assert_route_avoids planted modules [HSFormal.LTheory, HSFormal.Newman]
  constants [HSFormal.padicExclusion, HSFormal.newman_rigidity']

/--
info: route audit: 'HSBridge.PurityTest.usesNewman' avoids modules under HSFormal.LTheory and the
  constants HSFormal.padicExclusion
-/
#guard_msgs (whitespace := lax) in
#assert_route_avoids usesNewman modules [HSFormal.LTheory] constants [HSFormal.padicExclusion]

-- The import boundary: no module of OpenAI's route imports HS_proof; the bridge's modules do.

/-- info: import boundary: no imported module of 'HilbertSmith' imports HS_proof -/
#guard_msgs (whitespace := lax) in
#assert_import_boundary HilbertSmith

/--
error: import boundary: these modules of 'HSBridge' import HS_proof:
  HSBridge.PurityFixtures.Tainted
  HSBridge.PurityFixtures.TwinHS
  HSBridge.PurityFixtures.TwinClean
  HSBridge.Statements
-/
#guard_msgs (whitespace := lax) in
#assert_import_boundary HSBridge

end HSBridge.PurityTest
