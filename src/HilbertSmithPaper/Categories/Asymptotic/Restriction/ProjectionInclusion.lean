import HilbertSmithPaper.Categories.Asymptotic.Restriction.CoordinateProjection
import HilbertSmithPaper.Categories.Asymptotic.Restriction.DiagonalProjection
import HilbertSmithPaper.Categories.Asymptotic.Restriction.RestrictionIndexMem

/-!
# Inclusion after projection

For a restriction `M_P`, the coordinate projection followed by the coordinate inclusion is the
diagonal coordinate projection `trunc P`: `ιιᵀ` is diagonal with `1` exactly at the basis elements
whose index is enumerated, which are those with `P`.
-/

open CategoryTheory CategoryTheory.Limits Filter Topology

namespace HSP

variable {p : ℕ} {G : GroupSeq p} {X : Type*} [MetricSpace X] [AddAction (ZMod p) X]

namespace AsymPre

private theorem inclMat_apply_emb {H : Type} [DecidableEq H] {m m' : ℕ} {e : Fin m → Fin m'}
    (he : Function.Injective e) (g : H) (k : Fin m) (b : H × Fin m) :
    FreeCat.inclMat e (g, e k) b = if b = (g, k) then 1 else 0 := by
  obtain ⟨g', k'⟩ := b
  simp only [FreeCat.inclMat, Prod.mk.injEq, he.eq_iff]
  by_cases h1 : g = g' <;> by_cases h2 : k = k' <;> simp [h1, h2, eq_comm]

private theorem incl_mul_inclT {H : Type} [DecidableEq H] [Fintype H] {m m' : ℕ}
    {e : Fin m → Fin m'} (he : Function.Injective e) (Q : Fin m' → Prop) [DecidablePred Q]
    (hQ : ∀ j, Q j ↔ ∃ k, e k = j) :
    FreeCat.inclMat (G := H) e * (FreeCat.inclMat (G := H) e).transpose =
      Matrix.diagonal fun b => if Q b.2 then 1 else 0 := by
  ext ⟨g, j⟩ a'
  rw [Matrix.mul_apply, Matrix.diagonal_apply]
  simp only [Matrix.transpose_apply]
  by_cases hj : Q j
  · obtain ⟨k, rfl⟩ := (hQ j).1 hj
    simp only [inclMat_apply_emb he, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq' Finset.univ]
    simp only [Finset.mem_univ, ↓reduceIte, FreeCat.inclMat, hj]
    by_cases h : a' = (g, e k)
    · simp [h]
    · simp only [h, ↓reduceIte]
      exact (ite_eq_right_iff.2 fun e => absurd e.symm h).symm
  · rw [Finset.sum_eq_zero fun b _ => ?_]
    · simp [hj]
    · have : FreeCat.inclMat (G := H) e (g, j) b = 0 := by
        simp only [FreeCat.inclMat, Prod.mk.injEq]
        exact ite_eq_right_iff.2 fun h => absurd ((hQ j).2 ⟨b.2, h.2.symm⟩) hj
      rw [this, zero_mul]

variable (M : AsymPre G X) (P : ∀ i, Fin (M.n i) → Prop)

variable {M P} in
omit [MetricSpace X] [AddAction (ZMod p) X] in
open scoped Classical in
private theorem exists_restrictEmb_eq {i : ℕ} {j : Fin (M.n i)} (h : P i j) :
    ∃ k, M.restrictEmb P i k = j := by
  have hj : j ∈ Set.range ((Finset.univ.filter (P i)).orderEmbOfFin rfl) := by
    rw [Finset.range_orderEmbOfFin]; simpa using h
  exact hj

variable [∀ i, DecidablePred (P i)]

/-- The coordinate inclusion after the coordinate projection is the diagonal projection onto
the indices with `P`. -/
theorem restrictPro_restrictInc : M.restrictPro P ≫ M.restrictInc P = M.trunc P := by
  refine hom_ext fun i => FreeCat.hom_ext ?_
  have hQ : ∀ j, P i j ↔ ∃ k, M.restrictEmb P i k = j :=
    fun _ => ⟨exists_restrictEmb_eq, by rintro ⟨k, rfl⟩; exact restrictEmb_mem k⟩
  exact incl_mul_inclT (H := G.G i) (M.restrictEmb P i).injective (P i) hQ

end AsymPre

end HSP
