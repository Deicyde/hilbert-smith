import HilbertSmithPaper.Categories.Asymptotic.Restriction.DiagonalProjection

/-!
# Factorization through a diagonal projection, columns

If every column of every `u_i` whose index lies outside `P` vanishes, then `trunc P ≫ u = u`.
-/

open CategoryTheory CategoryTheory.Limits Filter Topology

namespace HSP

variable {p : ℕ} {G : GroupSeq p} {X : Type*} [MetricSpace X] [AddAction (ZMod p) X]

namespace AsymPre

private theorem mul_diag_eq {H : Type} [DecidableEq H] [Fintype H] {m : ℕ} {B : Type*}
    (Q : Fin m → Prop) [DecidablePred Q] (u : Matrix B (H × Fin m) ℚ)
    (h : ∀ a b, u a b ≠ 0 → Q b.2) :
    (u * Matrix.diagonal fun b : H × Fin m => if Q b.2 then (1 : ℚ) else 0) = u := by
  ext a b
  rw [Matrix.mul_diagonal]
  by_cases hb : Q b.2
  · simp [hb]
  · have : u a b = 0 := by
      by_contra h'
      exact hb (h a b h')
    simp [hb, this]

variable (M : AsymPre G X) (P : ∀ i, Fin (M.n i) → Prop)

variable [∀ i, DecidablePred (P i)]

/-- If every column of `u_i` outside `P` vanishes, then `u` factors through the truncation. -/
theorem trunc_comp_eq {N : AsymPre G X} (u : M ⟶ N)
    (h : ∀ i a (b : G.G i × Fin (M.n i)), FreeCat.mat (coord u i) a b ≠ 0 → P i b.2) :
    M.trunc P ≫ u = u :=
  hom_ext fun i => FreeCat.hom_ext (by
    exact mul_diag_eq (H := G.G i) (P i) (FreeCat.mat (coord u i)) (h i))

end AsymPre

end HSP
