import HilbertSmithPaper.LTheory.Base.Groups.InducedMap
import HilbertSmithPaper.LTheory.Base.Pairs.IsoCobordism
import HilbertSmithPaper.LTheory.Base.Categories.UnitaryIsomorphism

/-!
# Unitary invariance

If `η : F ≅ G` is a unitary natural isomorphism of duality functors `B → B'`, then
`F_* = G_* : L_k(B) → L_k(B')`: `η_C : F C → G C` is an isomorphism of complexes, and naturality
and unitarity give `η_{C %} F_% φ = G_% φ`, so the two classes are cobordant (an isomorphism of
Poincaré complexes is a cobordism).
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

open DualCat

universe v₁ v₂ u₁ u₂

variable {B : Type u₁} [Category.{v₁} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B]
  {B' : Type u₂} [Category.{v₂} B'] [Preadditive B'] [Linear ℚ B'] [HasFiniteBiproducts B']
  [DualCat B']

/-- `η^* ∘ ξ⁻¹ ∘ η_{M^*} = ζ⁻¹` for a unitary `η : (F, ξ) ≅ (G, ζ)`. -/
private lemma unitary_inv {F G : DualFunctor B B'} (η : DualFunctor.UnitaryIso F G) (M : B) :
    dualHom (η.iso.hom.app M) ≫ (F.ξ M).inv ≫ η.iso.hom.app (dual M) = (G.ξ M).inv := by
  have hd : dualHom (η.iso.hom.app M) ≫ dualHom (η.iso.inv.app M) = 𝟙 _ := by
    rw [← dualHom_comp, Iso.inv_hom_id_app, dualHom_id]
  have hY : ((F.ξ M).inv ≫ η.iso.hom.app (dual M) ≫ (G.ξ M).hom) ≫
      dualHom (η.iso.hom.app M) = 𝟙 _ := by
    simp only [Category.assoc]
    rw [η.unitary M, Iso.inv_hom_id]
  rw [← cancel_mono (G.ξ M).hom, Iso.inv_hom_id]
  simp only [Category.assoc]
  calc dualHom (η.iso.hom.app M) ≫ (F.ξ M).inv ≫ η.iso.hom.app (dual M) ≫ (G.ξ M).hom
      = dualHom (η.iso.hom.app M) ≫ ((F.ξ M).inv ≫ η.iso.hom.app (dual M) ≫ (G.ξ M).hom) ≫
          (dualHom (η.iso.hom.app M) ≫ dualHom (η.iso.inv.app M)) := by
        rw [hd, Category.comp_id]
    _ = dualHom (η.iso.hom.app M) ≫ (((F.ξ M).inv ≫ η.iso.hom.app (dual M) ≫ (G.ξ M).hom) ≫
          dualHom (η.iso.hom.app M)) ≫ dualHom (η.iso.inv.app M) := by
        simp only [Category.assoc]
    _ = dualHom (η.iso.hom.app M) ≫ dualHom (η.iso.inv.app M) := by
        rw [hY, Category.id_comp]
    _ = 𝟙 _ := hd

/-- If `η : F ≅ G` is a unitary natural isomorphism, then `F_* = G_*` on `L_k(B)`. -/
theorem LGroup.map_eq_of_unitaryIso {F G : DualFunctor B B'} (η : DualFunctor.UnitaryIso F G)
    (k : ℤ) : LGroup.map F k = LGroup.map G k :=
  AddMonoidHom.ext fun a => Quotient.inductionOn a fun x =>
    Quotient.sound (Cobordant.of_iso (x.map F) (x.map G)
      ((NatIso.mapHomologicalComplex η.iso _).app x.C) (by
        funext ⟨⟨p, q⟩, h⟩
        erw [StructureCx.push_apply]
        change dualHom (η.iso.hom.app (x.C.X q)) ≫
            ((F.ξ (x.C.X q)).inv ≫ F.toFunctor.map (x.φ ⟨(p, q), h⟩)) ≫
              η.iso.hom.app (x.C.X p) =
          (G.ξ (x.C.X q)).inv ≫ G.toFunctor.map (x.φ ⟨(p, q), h⟩)
        rw [Category.assoc, η.iso.hom.naturality, ← Category.assoc, ← Category.assoc,
          Category.assoc (dualHom _), unitary_inv]))

end HSP
