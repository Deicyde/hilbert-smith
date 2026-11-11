import HilbertSmithPaper.Categories.Asymptotic.Restriction.DiagonalProjection

/-!
# Factorization through a diagonal projection, rows

If eventually every row of `u_i` whose index lies outside `P` vanishes, then
`[u] ≫ [trunc P] = [u]` in the asymptotic category.
-/

open CategoryTheory CategoryTheory.Limits Filter Topology

namespace HSP

variable {p : ℕ} {G : GroupSeq p} {X : Type*} [MetricSpace X] [AddAction (ZMod p) X]

namespace AsymPre

private theorem diag_mul_eq {H : Type} [DecidableEq H] [Fintype H] {m : ℕ} {B : Type*}
    (Q : Fin m → Prop) [DecidablePred Q] (u : Matrix (H × Fin m) B ℚ)
    (h : ∀ a b, u a b ≠ 0 → Q a.2) :
    ((Matrix.diagonal fun b : H × Fin m => if Q b.2 then (1 : ℚ) else 0) * u) = u := by
  ext a b
  rw [Matrix.diagonal_mul]
  by_cases ha : Q a.2
  · simp [ha]
  · have : u a b = 0 := by
      by_contra h'
      exact ha (h a b h')
    simp [ha, this]

variable (M : AsymPre G X) (P : ∀ i, Fin (M.n i) → Prop)

variable [∀ i, DecidablePred (P i)]

/-- If eventually every row of `u_i` outside `P` vanishes, then `[u]` factors through the
truncation. -/
theorem mkHom_comp_trunc_eq {N : AsymPre G X} (u : N ⟶ M)
    (h : ∀ᶠ i in atTop, ∀ (a : G.G i × Fin (M.n i)) b, FreeCat.mat (coord u i) a b ≠ 0 →
      P i a.2) :
    AsymCat.mkHom u ≫ AsymCat.mkHom (M.trunc P) = AsymCat.mkHom u := by
  rw [← Functor.map_comp, AsymCat.mkHom_eq_iff]
  filter_upwards [h] with i hi
  exact FreeCat.hom_ext (by exact diag_mul_eq (H := G.G i) (P i) (FreeCat.mat (coord u i)) hi)

end AsymPre

end HSP
