import HilbertSmithPaper.LTheory.Base.Pairs.SumOfPoincare

/-!
# Sum of Poincaré complexes

The sum `(C, φ) ⊕ (C', φ') = (C ⊞ C', φ ⊕ φ')` of strict `k`-dimensional symmetric Poincaré
complexes, a strict `k`-dimensional symmetric Poincaré complex by Sums of Poincaré complexes.

Lean: `SymPoincare.sum` chooses the complex given by `SymPoincare.exists_sum`; its defining
equation `sum_spec` identifies `((x.sum y).C, (x.sum y).φ)` with `(C ⊞ C', φ ⊕ φ')` in the Σ-type of
structured complexes, and `exists_sum_iso` restates it as an isomorphism carrying the structures.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

open DualCat

universe v u

variable {B : Type u} [Category.{v} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B]

namespace SymPoincare

/-- The sum `(C, φ) ⊕ (C', φ') = (C ⊞ C', φ ⊕ φ')`. -/
noncomputable def sum {k : ℤ} (x y : SymPoincare B k) : SymPoincare B k :=
  (exists_sum x y).choose

lemma sum_spec {k : ℤ} (x y : SymPoincare B k) :
    (⟨(sum x y).C, (sum x y).φ⟩ : Σ C : ChainComplex B ℤ, (StructureCx C).X k) =
      ⟨x.C ⊞ y.C, StructureCx.sum x.φ y.φ⟩ :=
  (exists_sum x y).choose_spec

private lemma exists_iso_of_sigma_eq {k : ℤ} {C₀ C : ChainComplex B ℤ}
    {φ₀ : (StructureCx C₀).X k} {φ : (StructureCx C).X k}
    (h : (⟨C₀, φ₀⟩ : Σ C : ChainComplex B ℤ, (StructureCx C).X k) = ⟨C, φ⟩) :
    ∃ u : C ≅ C₀, (StructureCx.push u.hom).f k φ = φ₀ := by
  obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.mp h
  obtain rfl := eq_of_heq h
  exact ⟨Iso.refl _, by rw [Iso.refl_hom, StructureCx.push_id]; rfl⟩

/-- The sum is isomorphic to `C ⊞ C'` through an isomorphism carrying `φ ⊕ φ'` to its structure. -/
lemma exists_sum_iso {k : ℤ} (x y : SymPoincare B k) :
    ∃ u : x.C ⊞ y.C ≅ (sum x y).C,
      (StructureCx.push u.hom).f k (StructureCx.sum x.φ y.φ) = (sum x y).φ :=
  exists_iso_of_sigma_eq (sum_spec x y)

end SymPoincare

end HSP
