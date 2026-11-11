import Mathlib
import HilbertSmithPaper.LTheory.Localization.Products.Bookkeeping.InclusionProjection
import HilbertSmithPaper.LTheory.Localization.Products.Bookkeeping.InclusionProjectionNe

/-!
# Differential of a tensor product on summands

For a duality pairing `(⊠, κ)` and complexes `C`, `D` with finitely many nonzero chain objects,
the differential of `C ⊗ D` followed by the projection onto the summand `C_p ⊠ D_q` is
`π_{p,q} d = (d ⊠ 1) π_{p+1,q} + (-1)^p (1 ⊠ d) π_{p,q+1}`.
-/

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Prod

namespace HSP

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {B : Type u₁} [Category.{v₁} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B]
  {E : Type u₂} [Category.{v₂} E] [Preadditive E] [Linear ℚ E] [HasFiniteBiproducts E]
  [DualCat E]
  {B'' : Type u₃} [Category.{v₃} B''] [Preadditive B''] [Linear ℚ B''] [HasFiniteBiproducts B'']
  [DualCat B'']
  (P : DualityPairing B E B'')

namespace cxProd

variable {C : ChainComplex B ℤ} {D : ChainComplex E ℤ}
  (hC : {r | ¬ IsZero (C.X r)}.Finite) (hD : {r | ¬ IsZero (D.X r)}.Finite)

/-- The differential on a summand: `ι_{p,q} ≫ d = (d ⊠ 1) ≫ ι_{p-1,q} + (-1)^p (1 ⊠ d) ≫ ι_{p,q-1}`
(with `p' = p - 1`, `q' = q - 1`). -/
private lemma ι_d {p q r r' p' q' : ℤ} (h : p + q = r) (hp : p' + 1 = p)
    (hq : q' + 1 = q) :
    ι P hC hD p q r ≫ (cxProd P C D hC hD).d r r' =
      P.tensor.map (C.d p p' ×ₘ 𝟙 (D.X q)) ≫ ι P hC hD p' q r' +
        p.negOnePow • (P.tensor.map (𝟙 (C.X p) ×ₘ D.d q q') ≫ ι P hC hD p q' r') := by
  have := P.hasMapBifunctor_of_finite hC hD
  have hp' : (ComplexShape.down ℤ).Rel p p' := hp
  have hq' : (ComplexShape.down ℤ).Rel q q' := hq
  rw [ι, HomologicalComplex.ιMapBifunctorOrZero_eq _ _ _ _ _ _ _ h,
    HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
    HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
    HomologicalComplex.mapBifunctor.d₁_eq' _ _ _ _ hp',
    HomologicalComplex.mapBifunctor.d₂_eq' _ _ _ _ _ hq']
  have e1 : ComplexShape.ε₁ (ComplexShape.down ℤ) (ComplexShape.down ℤ) (ComplexShape.down ℤ)
      (p, q) = 1 := rfl
  have e2 : ComplexShape.ε₂ (ComplexShape.down ℤ) (ComplexShape.down ℤ) (ComplexShape.down ℤ)
      (p, q) = p.negOnePow := rfl
  rw [e1, e2, one_smul]
  rfl

/-- **Differential of a tensor product on summands.** The differential followed by a projection:
`d ≫ π_{p,q} = π_{p+1,q} ≫ (d ⊠ 1) + (-1)^p π_{p,q+1} ≫ (1 ⊠ d)`
(with `p₁ = p + 1`, `q₁ = q + 1`). -/
lemma d_π {p q r r' p₁ q₁ : ℤ} (hr : r' + 1 = r) (h : p + q = r') (hp : p + 1 = p₁)
    (hq : q + 1 = q₁) :
    (cxProd P C D hC hD).d r r' ≫ π P hC hD p q r' =
      π P hC hD p₁ q r ≫ P.tensor.map (C.d p₁ p ×ₘ 𝟙 (D.X q)) +
        p.negOnePow • (π P hC hD p q₁ r ≫ P.tensor.map (𝟙 (C.X p) ×ₘ D.d q₁ q)) := by
  have := P.hasMapBifunctor_of_finite hC hD
  ext a b hab
  change a + b = r at hab
  have hι : HomologicalComplex.ιMapBifunctor C D (Functor.curry.obj P.tensor)
      (ComplexShape.down ℤ) a b r hab = ι P hC hD a b r :=
    (HomologicalComplex.ιMapBifunctorOrZero_eq _ _ _ _ _ _ _ hab).symm
  rw [hι, ← Category.assoc, ι_d P hC hD (r' := r') hab (sub_add_cancel a 1) (sub_add_cancel b 1)]
  simp only [Preadditive.comp_add, Preadditive.add_comp, Linear.units_smul_comp,
    Linear.comp_units_smul, Category.assoc]
  by_cases h1 : a = p₁ ∧ b = q
  · obtain ⟨rfl, rfl⟩ := h1
    have e : a - 1 = p := by omega
    subst e
    rw [ι_π_self P hC hD (p := a - 1) (q := b) (r := r') (by omega),
      ι_π_of_ne P hC hD (p := a) (q := b - 1) (p' := a - 1) (q' := b) (r := r') (by omega),
      ι_π_self_assoc P hC hD (p := a) (q := b) (r := r) hab,
      ι_π_of_ne_assoc P hC hD (p := a) (q := b) (p' := a - 1) (q' := q₁) (r := r) (by omega)]
    simp
  · by_cases h2 : a = p ∧ b = q₁
    · obtain ⟨rfl, rfl⟩ := h2
      have e : b - 1 = q := by omega
      subst e
      rw [ι_π_of_ne P hC hD (p := a - 1) (q := b) (p' := a) (q' := b - 1) (r := r') (by omega),
        ι_π_self P hC hD (p := a) (q := b - 1) (r := r') (by omega),
        ι_π_of_ne_assoc P hC hD (p := a) (q := b) (p' := p₁) (q' := b - 1) (r := r) (by omega),
        ι_π_self_assoc P hC hD (p := a) (q := b) (r := r) hab]
      simp
    · rw [ι_π_of_ne P hC hD (p := a - 1) (q := b) (p' := p) (q' := q) (r := r') (by omega),
        ι_π_of_ne P hC hD (p := a) (q := b - 1) (p' := p) (q' := q) (r := r') (by omega),
        ι_π_of_ne_assoc P hC hD (p := a) (q := b) (p' := p₁) (q' := q) (r := r) h1,
        ι_π_of_ne_assoc P hC hD (p := a) (q := b) (p' := p) (q' := q₁) (r := r) h2]
      simp

end cxProd

end HSP
