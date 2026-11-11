import HilbertSmithPaper.Categories.Asymptotic.Restriction.DiagonalProjection

/-!
# Product of diagonal projections

The composite of the diagonal coordinate projections onto `P` and onto `Q` is the diagonal
coordinate projection onto `P ∧ Q`.
-/

open CategoryTheory CategoryTheory.Limits Filter Topology

namespace HSP

variable {p : ℕ} {G : GroupSeq p} {X : Type*} [MetricSpace X] [AddAction (ZMod p) X]

namespace AsymPre

private theorem diag_mul_diag {H : Type} [DecidableEq H] [Fintype H] {m : ℕ}
    (Q Q' : Fin m → Prop) [DecidablePred Q] [DecidablePred Q'] :
    ((Matrix.diagonal fun b : H × Fin m => if Q' b.2 then (1 : ℚ) else 0) *
      Matrix.diagonal fun b : H × Fin m => if Q b.2 then (1 : ℚ) else 0) =
      Matrix.diagonal fun b : H × Fin m => if Q b.2 ∧ Q' b.2 then (1 : ℚ) else 0 := by
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext b
  by_cases h : Q b.2 <;> by_cases h' : Q' b.2 <;> simp [h, h']

variable (M : AsymPre G X) (P : ∀ i, Fin (M.n i) → Prop)

variable [∀ i, DecidablePred (P i)]

/-- `trunc P ≫ trunc Q = trunc (P ∧ Q)`. -/
theorem trunc_comp_trunc (Q : ∀ i, Fin (M.n i) → Prop) [∀ i, DecidablePred (Q i)] :
    M.trunc P ≫ M.trunc Q = M.trunc (fun i k => P i k ∧ Q i k) :=
  hom_ext fun i => FreeCat.hom_ext (by exact diag_mul_diag (H := G.G i) (P i) (Q i))

end AsymPre

end HSP
