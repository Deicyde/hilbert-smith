import Mathlib.Topology.Algebra.Group.Basic

/-!
# A fixture for the route-separation audit: a clean copy of a realized lemma

This module imports Mathlib only. Its one theorem makes Lean realize the congruence lemma
`Homeomorph.addRight.congr_simp` here, so the build then holds two copies of that lemma: this one,
and the one Lean realized inside HS_proof's module `HSFormal.ChartData`. `HSBridge.PurityTest`
imports this module before HS_proof, so Lean's index of declaring modules names this module, and
the test checks that the audit nevertheless reports the lemma's provenance as ambiguous.
-/

namespace HSBridge.PurityFixtures

/-- A use of `Homeomorph.addRight.congr_simp` that makes Lean realize the lemma in this module. -/
theorem addRight_congr {G : Type*} [TopologicalSpace G] [AddGroup G] [ContinuousAdd G] (x y : G)
    (h : x = y) : Homeomorph.addRight x = Homeomorph.addRight y :=
  Homeomorph.addRight.congr_simp x y h

end HSBridge.PurityFixtures
