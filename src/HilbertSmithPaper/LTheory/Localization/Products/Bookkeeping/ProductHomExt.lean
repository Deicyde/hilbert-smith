import Mathlib
import HilbertSmithPaper.LTheory.Localization.Products.Bookkeeping.ProductTotal

/-!
# Maps into a tensor product are determined by their components

For a duality pairing `(⊠, κ)` and complexes `C`, `D` with finitely many nonzero chain objects,
two maps `f, g : Z → (C ⊗ D)_r` with `π_{p,q} f = π_{p,q} g` for all `p + q = r` are equal.
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

/-- **Maps into a tensor product are determined by their components.** -/
lemma hom_ext_to {r : ℤ} {Z : B''} {f g : Z ⟶ (cxProd P C D hC hD).X r}
    (h : ∀ p q, p + q = r → f ≫ π P hC hD p q r = g ≫ π P hC hD p q r) : f = g := by
  rw [← Category.comp_id f, ← Category.comp_id g, ← total P hC hD r, Preadditive.comp_sum,
    Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [← Category.assoc, ← Category.assoc, h x.1 x.2 ((mem_supp hC hD).1 hx).2]

end cxProd

end HSP
