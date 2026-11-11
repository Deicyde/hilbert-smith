import HilbertSmithPaper.LTheory.Base.Groups.InducedMap
import HilbertSmithPaper.LTheory.Base.Pairs.IsoCobordism

/-!
# Identity induces the identity

For a duality category `B`, `(id_B)_* = id` on `L_k(B)`: the identity functor fixes every complex,
and `id_% φ = φ`.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

open DualCat

universe v u

variable {B : Type u} [Category.{v} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B]

/-- `(id_B)_* = id` on `L_k(B)`. -/
theorem LGroup.map_id (k : ℤ) : LGroup.map (DualFunctor.id B) k = AddMonoidHom.id _ :=
  AddMonoidHom.ext fun a => Quotient.inductionOn a fun x =>
    Quotient.sound (Cobordant.of_iso (x.map (DualFunctor.id B)) x (Iso.refl _) (by
      funext ⟨⟨p, q⟩, h⟩
      erw [StructureCx.push_apply]
      change dualHom (𝟙 (x.C.X q)) ≫ (((DualFunctor.id B).ξ (x.C.X q)).inv ≫
        x.φ ⟨(p, q), h⟩) ≫ 𝟙 (x.C.X p) = x.φ ⟨(p, q), h⟩
      simp only [dualHom_id, Category.id_comp, Category.comp_id, DualFunctor.id_ξ, Iso.refl_inv]
      exact Category.id_comp _))

end HSP
