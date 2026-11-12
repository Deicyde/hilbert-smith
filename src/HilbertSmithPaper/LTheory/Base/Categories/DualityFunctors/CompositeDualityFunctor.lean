import HilbertSmithPaper.LTheory.Base.Categories.DualityFunctor

/-!
# Identity and composite duality functors

The identity duality functor is `𝟭 A` with `ξ = id`. The composite `(G, ζ) ∘ (F, ξ)` of duality
functors is `F ⋙ G` with `ξ^{GF}_M = ζ_{F M} ∘ G (ξ_M)`.

## Encoding

`HSP.DualFunctor.id` and `HSP.DualFunctor.comp` (the declarations of the article), with `simps`
lemmas for their components.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

open DualCat

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace DualFunctor

variable {A : Type u₁} [Category.{v₁} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A]
  {B : Type u₂} [Category.{v₂} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B]
  {E : Type u₃} [Category.{v₃} E] [Preadditive E] [Linear ℚ E] [HasFiniteBiproducts E]
  [DualCat E]

/-- The identity duality functor, with `ξ = id`. -/
@[simps]
def id (A : Type u₁) [Category.{v₁} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
    [DualCat A] : DualFunctor A A where
  toFunctor := 𝟭 A
  ξ M := Iso.refl _
  ξ_natural f := by simp
  ξ_dual M := by simp

/-- The composite `(G, ζ) ∘ (F, ξ)` of duality functors, with `ξ^{GF}_M = ζ_{F M} ∘ G (ξ_M)`. -/
@[simps]
def comp (F : DualFunctor A B) (G : DualFunctor B E) : DualFunctor A E where
  toFunctor := F.toFunctor ⋙ G.toFunctor
  ξ M := G.toFunctor.mapIso (F.ξ M) ≪≫ G.ξ (F.toFunctor.obj M)
  ξ_natural {M N} f := by
    have h1 := F.ξ_natural f
    have h2 := G.ξ_natural (F.toFunctor.map f)
    simp only [Functor.comp_obj, Functor.comp_map, Iso.trans_hom, Functor.mapIso_hom]
    rw [← Category.assoc, ← G.toFunctor.map_comp, h1, G.toFunctor.map_comp, Category.assoc, h2,
      Category.assoc]
  ξ_dual M := by
    simp only [Functor.comp_obj, Iso.trans_hom, Functor.mapIso_hom, DualCat.dualHom_comp]
    rw [G.ξ_dual]
    have h := G.ξ_natural (F.ξ M).hom
    have hinv : dualHom (G.toFunctor.map (F.ξ M).hom) = (G.ξ (dual (F.toFunctor.obj M))).inv ≫
        G.toFunctor.map (dualHom (F.ξ M).hom) ≫ (G.ξ (F.toFunctor.obj (dual M))).hom := by
      rw [h, Iso.inv_hom_id_assoc]
    rw [hinv, F.ξ_dual, G.toFunctor.map_comp, eqToHom_map]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, eqToHom_trans_assoc]

end DualFunctor

end HSP
