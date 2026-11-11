import HilbertSmithPaper.LTheory.Base.Groups.InducedMap
import HilbertSmithPaper.LTheory.Base.Pairs.IsoCobordism

/-!
# Functoriality of induced maps

For duality functors `F : B → B'` and `G : B' → B''`, `(G ∘ F)_* = G_* ∘ F_*` on `L_k(B)`:
`(G F) C = G (F C)`, and the composite `ξ` gives `(G F)_% φ = G_% F_% φ`.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

open DualCat

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {B : Type u₁} [Category.{v₁} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B]
  {B' : Type u₂} [Category.{v₂} B'] [Preadditive B'] [Linear ℚ B'] [HasFiniteBiproducts B']
  [DualCat B']
  {B'' : Type u₃} [Category.{v₃} B''] [Preadditive B''] [Linear ℚ B''] [HasFiniteBiproducts B'']
  [DualCat B'']

/-- `(G ∘ F)_* = G_* ∘ F_*` on `L_k(B)`. -/
theorem LGroup.map_comp (F : DualFunctor B B') (G : DualFunctor B' B'') (k : ℤ) :
    LGroup.map (F.comp G) k = (LGroup.map G k).comp (LGroup.map F k) :=
  AddMonoidHom.ext fun a => Quotient.inductionOn a fun x =>
    Quotient.sound (Cobordant.of_iso (x.map (F.comp G)) ((x.map F).map G) (Iso.refl _) (by
      funext ⟨⟨p, q⟩, h⟩
      erw [StructureCx.push_apply, dualHom_id, Category.id_comp, Category.comp_id]
      change ((F.comp G).ξ (x.C.X q)).inv ≫ G.toFunctor.map (F.toFunctor.map (x.φ ⟨(p, q), h⟩)) =
        (G.ξ (F.toFunctor.obj (x.C.X q))).inv ≫
          G.toFunctor.map ((F.ξ (x.C.X q)).inv ≫ F.toFunctor.map (x.φ ⟨(p, q), h⟩))
      simp only [DualFunctor.comp_ξ, Iso.trans_inv, Functor.mapIso_inv, Functor.map_comp]
      exact Category.assoc _ _ _))

end HSP
