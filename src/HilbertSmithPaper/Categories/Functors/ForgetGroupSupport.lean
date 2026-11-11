import Mathlib
import HilbertSmithPaper.Categories.Functors.ForgetGroup
import HilbertSmithPaper.Categories.Supports.SupportSubcategory

/-!
# Forgetting the group preserves support

For an isometric action and an invariant `S ⊆ X`, forgetting the group carries `𝒜_S` into
`𝒜_S ⊆ 𝒜_𝟏(X)` (`HSP.forget_supp`): the new labels are `χ_i(g) x_i(k)`, and since `S` is
invariant and the action isometric, `χ_i(g) x_i(k)` is as close to `S` as `x_i(k)` is.

Lean encoding: invariance is `hS : ∀ c, ∀ x ∈ S, c +ᵥ x ∈ S`; closedness of `S` is not needed.
-/

open CategoryTheory Filter

namespace HSP

variable {p : ℕ} {G : GroupSeq p} {X : Type*} [MetricSpace X] [AddAction (ZMod p) X]
  [IsIsometricVAdd (ZMod p) X]

/-- Forgetting the group carries `𝒜_S` into `𝒜_S` for invariant `S`. -/
theorem forget_supp {S : Set X} (hS : ∀ (c : ZMod p), ∀ x ∈ S, c +ᵥ x ∈ S) {P : AsymCat G X}
    (hP : supp S P) : supp S ((forgetGroup (G := G) (X := X)).toFunctor.obj P) := by
  intro ε hε
  filter_upwards [hP ε hε] with i hi j
  obtain ⟨s, hs, hd⟩ := Metric.mem_thickening_iff.1
    (hi ((groupEnum (G.G i) (P.as.n i)).symm j).2)
  refine Metric.mem_thickening_iff.2 ⟨G.χ i ((groupEnum (G.G i) (P.as.n i)).symm j).1 +ᵥ s,
    hS _ _ hs, ?_⟩
  exact (dist_vadd (G.χ i ((groupEnum (G.G i) (P.as.n i)).symm j).1) _ s).trans_lt hd

end HSP
