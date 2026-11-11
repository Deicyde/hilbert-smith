import Mathlib
import HilbertSmithPaper.LTheory.Localization.Products.Bookkeeping.InclusionProjection
import HilbertSmithPaper.LTheory.Localization.Products.Bookkeeping.InclusionProjectionNe
import HilbertSmithPaper.LTheory.Localization.Products.Bookkeeping.SummandZero

/-!
# A tensor product is the sum of its summands

For a duality pairing `(⊠, κ)` and complexes `C`, `D` with finitely many nonzero chain objects,
`∑ ι_{p,q} ∘ π_{p,q} = 1` on `(C ⊗ D)_r`, the sum running over the support of degree `r`.
-/

open CategoryTheory CategoryTheory.Limits

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

/-- **A tensor product is the sum of its summands.** `∑ π_{p,q} ≫ ι_{p,q} = 𝟙`. -/
lemma total (r : ℤ) :
    ∑ x ∈ supp hC hD r, π P hC hD x.1 x.2 r ≫ ι P hC hD x.1 x.2 r = 𝟙 _ := by
  have := P.hasMapBifunctor_of_finite hC hD
  ext p q h
  change p + q = r at h
  rw [Preadditive.comp_sum, Category.comp_id]
  have hι : HomologicalComplex.ιMapBifunctor C D (Functor.curry.obj P.tensor)
      (ComplexShape.down ℤ) p q r h = ι P hC hD p q r :=
    (HomologicalComplex.ιMapBifunctorOrZero_eq _ _ _ _ _ _ _ h).symm
  rw [hι]
  by_cases hx : (p, q) ∈ supp hC hD r
  · rw [Finset.sum_eq_single (p, q)]
    · rw [← Category.assoc, ι_π_self P hC hD h]
      exact Category.id_comp _
    · rintro ⟨p', q'⟩ _ hne
      rw [← Category.assoc, ι_π_of_ne P hC hD (fun h' => hne (by rw [h'.1, h'.2])), zero_comp]
    · exact fun h' => absurd hx h'
  · rw [(isZero_of_not_mem_supp P hC hD h hx).eq_of_src (ι P hC hD p q r) 0,
      Finset.sum_eq_zero fun _ _ => zero_comp]

end cxProd

end HSP
