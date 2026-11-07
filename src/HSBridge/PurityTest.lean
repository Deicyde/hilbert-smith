import HilbertSmith
import HSBridge.Purity
import HSBridge.Statements
import HSFormal.Universe

/-!
# Tests for the route-separation audit

These tests are part of the build: each `#guard_msgs` fails the build if the audit's verdict
changes. They show that `#assert_route_pure` catches a theorem that uses HS_proof's
`HSFormal.padicExclusion`, directly or through our own declarations, and also a declaration of
`HSFormal` outside the `HSFormal` namespace; that it passes honest theorems; and that its
allow-list admits exactly the paths through the allowed constants. The last test checks the import
boundary: no module of the library `HilbertSmith` imports `HSFormal`.

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

/-- A use of a constant that lies outside the `HSFormal` namespace but belongs to an `HSFormal`
module: the congruence lemma of Mathlib's `Homeomorph.addRight`, which Lean generated inside
HS_proof. The audit attributes constants by module, so it reports this (harmless) use: it errs on
the safe side. -/
theorem outsideNamespace (x y : ℝ) (h : x = y) :
    Homeomorph.addRight x = Homeomorph.addRight y :=
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

/-! ### The audit's verdicts -/

-- Planted violations are caught: directly, through a declaration of our own, as an ex-falso
-- interface field, and next to an allowed constant.

/--
error: route audit: 'HSBridge.PurityTest.planted' depends on HSFormal; entry points:
  HSFormal.PadicExclusion
  HSFormal.padicExclusion
-/
#guard_msgs in
#assert_route_pure planted

/--
error: route audit: 'HSBridge.PurityTest.laundered' depends on HSFormal; entry points:
  HSFormal.PadicExclusion
  HSFormal.padicExclusion
-/
#guard_msgs in
#assert_route_pure laundered

/--
error: route audit: 'HSBridge.PurityTest.fakeInterface' depends on HSFormal; entry points:
  HSFormal.PadicExclusion
  HSFormal.padicExclusion
-/
#guard_msgs in
#assert_route_pure fakeInterface

/--
error: route audit: 'HSBridge.PurityTest.plantedWithNewman' depends on HSFormal; entry points:
  HSFormal.PadicExclusion
  HSFormal.padicExclusion
-/
#guard_msgs in
#assert_route_pure plantedWithNewman allowing HSBridge.newmanInput

/--
error: route audit: 'HSFormal.padicExclusion' depends on HSFormal; entry points:
  HSFormal.padicExclusion
-/
#guard_msgs in
#assert_route_pure HSFormal.padicExclusion

-- Constants are attributed by module, so a constant outside the `HSFormal` namespace is caught.

/--
error: route audit: 'HSBridge.PurityTest.outsideNamespace' depends on HSFormal; entry points:
  Homeomorph.addRight.congr_simp
-/
#guard_msgs in
#assert_route_pure outsideNamespace

-- Honest declarations pass: our own, a theorem of OpenAI's route, and the compared statement.

/-- info: route audit: 'HSBridge.PurityTest.honest' depends on no constant from HSFormal -/
#guard_msgs in
#assert_route_pure honest

/-- info: route audit: 'HilbertSmith.closed_eq_dvd_pow' depends on no constant from HSFormal -/
#guard_msgs in
#assert_route_pure HilbertSmith.closed_eq_dvd_pow

/-- info: route audit: 'HilbertSmith.Statements.PadicExclusion' depends on no constant from HSFormal -/
#guard_msgs in
#assert_route_pure HilbertSmith.Statements.PadicExclusion

-- The allow-list admits exactly the paths through the allowed constants, and a stale entry fails.

/--
error: route audit: 'HSBridge.PurityTest.usesNewman' depends on HSFormal; entry points:
  HSFormal.newman_rigidity'
  HSFormal.Newman.newmanPrimeOrder
-/
#guard_msgs in
#assert_route_pure usesNewman

/--
info: route audit: 'HSBridge.PurityTest.usesNewman' depends on no constant from HSFormal except through:
  HSBridge.newmanInput
-/
#guard_msgs in
#assert_route_pure usesNewman allowing HSBridge.newmanInput

/--
info: route audit: 'HSBridge.PurityTest.laundered' depends on no constant from HSFormal except through:
  HSBridge.PurityTest.planted
-/
#guard_msgs in
#assert_route_pure laundered allowing planted

/--
error: route audit: 'HSBridge.PurityTest.planted' does not depend on the allowed constants:
  HSBridge.newmanInput
-/
#guard_msgs in
#assert_route_pure planted allowing HSBridge.newmanInput

-- The report counts what a declaration reaches inside `HSFormal`, by module.

/-- info: route audit: 'HSBridge.PurityTest.honest' depends on no constant from HSFormal -/
#guard_msgs in
#route_report honest

/--
info: route audit: 'HSBridge.PurityTest.usesNewman' depends on 376 constants from HSFormal; by module:
  HSFormal.MontgomeryPrime: 5
  HSFormal.Newman: 370
  HSFormal.WeakInputs: 1
entry points into HSFormal:
  HSFormal.newman_rigidity'
  HSFormal.Newman.newmanPrimeOrder
-/
#guard_msgs in
#route_report usesNewman

-- The import boundary: no module of OpenAI's route imports HS_proof; the bridge's modules do.
/-- info: import boundary: no imported module of 'HilbertSmith' imports HSFormal -/
#guard_msgs in
#assert_import_boundary HilbertSmith

/--
error: import boundary: these modules of 'HSBridge' import HSFormal:
  HSBridge.Statements
-/
#guard_msgs in
#assert_import_boundary HSBridge

end HSBridge.PurityTest
