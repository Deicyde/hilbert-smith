import HilbertSmithPaper.Categories.Asymptotic.Restriction.DiagonalProjection

/-!
# Complementary diagonal projection

The diagonal coordinate projection onto the indices without `P` is `1 - trunc P`.
-/

open CategoryTheory CategoryTheory.Limits Filter Topology

namespace HSP

variable {p : ℕ} {G : GroupSeq p} {X : Type*} [MetricSpace X] [AddAction (ZMod p) X]

namespace AsymPre

private theorem diag_not {H : Type} [DecidableEq H] {m : ℕ} (Q : Fin m → Prop)
    [DecidablePred Q] :
    (Matrix.diagonal fun b : H × Fin m => if ¬Q b.2 then (1 : ℚ) else 0) =
      1 - Matrix.diagonal fun b : H × Fin m => if Q b.2 then (1 : ℚ) else 0 := by
  rw [← Matrix.diagonal_one, Matrix.diagonal_sub]
  congr 1
  funext b
  by_cases h : Q b.2 <;> simp [h]

variable (M : AsymPre G X) (P : ∀ i, Fin (M.n i) → Prop)

variable [∀ i, DecidablePred (P i)]

/-- `trunc ¬P = 1 - trunc P`. -/
theorem trunc_not : M.trunc (fun i k => ¬P i k) = 𝟙 M - M.trunc P :=
  hom_ext fun i => FreeCat.hom_ext (by exact diag_not (H := G.G i) (P i))

end AsymPre

end HSP
