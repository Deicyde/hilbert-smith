import Mathlib
import HilbertSmithPaper.LTheory.Base.Categories.DualityCategory

/-!
# Duality pairings

A duality pairing `(⊠, κ) : B × E → B''` between duality categories is a ℚ-bilinear functor
`⊠ : B × E ⥤ B''` (a functor on the product category whose action on morphisms,
`f ⊠ g = ⊠.map (f ×ₘ g)`, is additive and ℚ-homogeneous in each variable separately) together with
isomorphisms `κ N V : (N ⊠ V)^* ≅ N^* ⊠ V^*`, natural in both variables, such that
`(κ N V)^* = κ (N^*) (V^*)` as maps `(N^* ⊠ V^*)^* → N ⊠ V`. The last equation is stated with
the transport along `N^{**} ⊠ V^{**} = N ⊠ V = (N ⊠ V)^{**}`, since these identities hold only
propositionally.
-/

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Prod

namespace HSP

open DualCat

universe v₁ v₂ v₃ u₁ u₂ u₃

/-- A *duality pairing* `(⊠, κ) : B × E → B''`: a ℚ-bilinear functor `⊠ : B × E ⥤ B''` and
isomorphisms `κ N V : (N ⊠ V)^* ≅ N^* ⊠ V^*`, natural in both variables, with
`(κ N V)^* = κ (N^*) (V^*)` (up to the canonical transports). -/
structure DualityPairing (B : Type u₁) [Category.{v₁} B] [Preadditive B] [Linear ℚ B]
    [HasFiniteBiproducts B] [DualCat B]
    (E : Type u₂) [Category.{v₂} E] [Preadditive E] [Linear ℚ E] [HasFiniteBiproducts E]
    [DualCat E]
    (B'' : Type u₃) [Category.{v₃} B''] [Preadditive B''] [Linear ℚ B''] [HasFiniteBiproducts B'']
    [DualCat B''] where
  /-- The functor `⊠ : B × E ⥤ B''`. -/
  tensor : B × E ⥤ B''
  /-- `⊠` is additive in the first variable. -/
  map_add_left {N N' : B} {V V' : E} (f f' : N ⟶ N') (g : V ⟶ V') :
    tensor.map ((f + f') ×ₘ g) = tensor.map (f ×ₘ g) + tensor.map (f' ×ₘ g)
  /-- `⊠` is additive in the second variable. -/
  map_add_right {N N' : B} {V V' : E} (f : N ⟶ N') (g g' : V ⟶ V') :
    tensor.map (f ×ₘ (g + g')) = tensor.map (f ×ₘ g) + tensor.map (f ×ₘ g')
  /-- `⊠` is ℚ-homogeneous in the first variable. -/
  map_smul_left {N N' : B} {V V' : E} (c : ℚ) (f : N ⟶ N') (g : V ⟶ V') :
    tensor.map ((c • f) ×ₘ g) = c • tensor.map (f ×ₘ g)
  /-- `⊠` is ℚ-homogeneous in the second variable. -/
  map_smul_right {N N' : B} {V V' : E} (c : ℚ) (f : N ⟶ N') (g : V ⟶ V') :
    tensor.map (f ×ₘ (c • g)) = c • tensor.map (f ×ₘ g)
  /-- The isomorphism `κ N V : (N ⊠ V)^* ≅ N^* ⊠ V^*`. -/
  κ (N : B) (V : E) : dual (tensor.obj (N, V)) ≅ tensor.obj (dual N, dual V)
  /-- Naturality: `κ_{N,V} ∘ (f ⊠ g)^* = (f^* ⊠ g^*) ∘ κ_{N',V'}`. -/
  κ_natural {N N' : B} {V V' : E} (f : N ⟶ N') (g : V ⟶ V') :
    dualHom (tensor.map (f ×ₘ g)) ≫ (κ N V).hom =
      (κ N' V').hom ≫ tensor.map (dualHom f ×ₘ dualHom g)
  /-- `(κ N V)^* = κ (N^*) (V^*)`, with the transport along
  `N^{**} ⊠ V^{**} = N ⊠ V = (N ⊠ V)^{**}`. -/
  κ_dual (N : B) (V : E) :
    dualHom (κ N V).hom = (κ (dual N) (dual V)).hom ≫
      eqToHom (by rw [dual_dual, dual_dual, dual_dual])

end HSP
