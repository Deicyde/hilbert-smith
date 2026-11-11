import HilbertSmithPaper.Categories.Asymptotic.Restriction.CoordinateProjection

/-!
# Projection after inclusion

For a restriction `M_P`, the coordinate inclusion followed by the coordinate projection is the
identity: `ιᵀι = 1` because the enumeration of the indices with `P` is injective.
-/

open CategoryTheory CategoryTheory.Limits Filter Topology

namespace HSP

variable {p : ℕ} {G : GroupSeq p} {X : Type*} [MetricSpace X] [AddAction (ZMod p) X]

namespace AsymPre

private theorem inclT_mul_incl {H : Type} [DecidableEq H] [Fintype H] {m m' : ℕ}
    {e : Fin m → Fin m'} (he : Function.Injective e) :
    (FreeCat.inclMat (G := H) e).transpose * FreeCat.inclMat (G := H) e = 1 := by
  ext ⟨g, k⟩ ⟨g', k'⟩
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Matrix.transpose_apply, FreeCat.inclMat, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq' Finset.univ]
  simp only [Finset.mem_univ, ↓reduceIte, Prod.mk.injEq, he.eq_iff]

variable (M : AsymPre G X) (P : ∀ i, Fin (M.n i) → Prop)

/-- The coordinate projection after the coordinate inclusion is the identity of `M_P`. -/
theorem restrictInc_restrictPro : M.restrictInc P ≫ M.restrictPro P = 𝟙 _ :=
  hom_ext fun i => FreeCat.hom_ext (by
    exact inclT_mul_incl (H := G.G i) (M.restrictEmb P i).injective)

end AsymPre

end HSP
