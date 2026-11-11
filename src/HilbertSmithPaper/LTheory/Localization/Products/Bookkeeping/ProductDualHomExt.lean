import Mathlib
import HilbertSmithPaper.LTheory.Localization.Products.Bookkeeping.ProductTotal

/-!
# Maps out of the dual of a tensor product are determined by their components

For a duality pairing `(⊠, κ)` and complexes `C`, `D` with finitely many nonzero chain objects,
two maps `f, g : ((C ⊗ D)_r)^* → Z` with `f π_{p,q}^* = g π_{p,q}^*` for all `p + q = r` are
equal.
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

private lemma dualHom_sum {M N : B''} {ι' : Type*} (s : Finset ι') (f : ι' → (M ⟶ N)) :
    DualCat.dualHom (∑ i ∈ s, f i) = ∑ i ∈ s, DualCat.dualHom (f i) :=
  map_sum (AddMonoidHom.mk' (DualCat.dualHom (M := M) (N := N)) DualCat.dualHom_add) f s

namespace cxProd

variable {C : ChainComplex B ℤ} {D : ChainComplex E ℤ}
  (hC : {r | ¬ IsZero (C.X r)}.Finite) (hD : {r | ¬ IsZero (D.X r)}.Finite)

/-- **Maps out of the dual of a tensor product are determined by their components.** -/
lemma dual_hom_ext {r : ℤ} {Z : B''} {f g : DualCat.dual ((cxProd P C D hC hD).X r) ⟶ Z}
    (h : ∀ p q, p + q = r →
      DualCat.dualHom (π P hC hD p q r) ≫ f = DualCat.dualHom (π P hC hD p q r) ≫ g) :
    f = g := by
  have h1 : 𝟙 (DualCat.dual ((cxProd P C D hC hD).X r)) =
      ∑ x ∈ supp hC hD r, DualCat.dualHom (ι P hC hD x.1 x.2 r) ≫
        DualCat.dualHom (π P hC hD x.1 x.2 r) := by
    rw [← DualCat.dualHom_id, ← total P hC hD r, dualHom_sum]
    simp only [DualCat.dualHom_comp]
  rw [← Category.id_comp f, ← Category.id_comp g, h1, Preadditive.sum_comp, Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Category.assoc, Category.assoc, h x.1 x.2 ((mem_supp hC hD).1 hx).2]

end cxProd

end HSP
