import HilbertSmithPaper.LTheory.Base.Groups.InducedMapComp
import HilbertSmithPaper.LTheory.Base.Categories.DualityFunctors.CompositeDualityFunctor
import HilbertSmithPaper.LTheory.Base.Groups.UnitaryInvariance

/-!
# Composites on L^p

For duality functors `F : A → A'` and `G : A' → A''`, `(G ∘ F)_* = G_* ∘ F_*` on `L^p_k(A)`.
`Kar(G ∘ F)` and `Kar G ∘ Kar F` have the same objects `(G F M, G F e)` and the same maps; their
duality isomorphisms at `(M, e)` agree, because `(F e)^* ξ_M = ξ_M F(e^*)` by naturality of `ξ` and
`e^*` is idempotent. So the identity maps form a unitary natural isomorphism between them; conclude
by unitary invariance and functoriality of induced maps.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents

namespace HSP

open DualCat

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {A : Type u₁} [Category.{v₁} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A]
  {A' : Type u₂} [Category.{v₂} A'] [Preadditive A'] [Linear ℚ A'] [HasFiniteBiproducts A']
  [DualCat A']
  {A'' : Type u₃} [Category.{v₃} A''] [Preadditive A''] [Linear ℚ A''] [HasFiniteBiproducts A'']
  [DualCat A'']

/-- The identity maps `Kar(G ∘ F) ≅ Kar G ∘ Kar F`, a unitary natural isomorphism. -/
private def karCompIso (F : DualFunctor A A') (G : DualFunctor A' A'') :
    DualFunctor.UnitaryIso (F.comp G).kar (F.kar.comp G.kar) where
  iso := NatIso.ofComponents (fun P => Iso.refl _) (fun f => by
    erw [Category.comp_id, Category.id_comp]
    rfl)
  unitary P := by
    apply Idempotents.Karoubi.hom_ext
    have hid : dualHom (F.toFunctor.map P.p) ≫ dualHom (F.toFunctor.map P.p) =
        dualHom (F.toFunctor.map P.p) := by
      rw [← dualHom_comp, ← F.toFunctor.map_comp, P.idem]
    change G.toFunctor.map (F.toFunctor.map (dualHom P.p)) ≫
        ((G.toFunctor.map (F.toFunctor.map (dualHom P.p) ≫ (F.ξ P.X).hom) ≫
          (G.toFunctor.map (dualHom (F.toFunctor.map P.p)) ≫ (G.ξ (F.toFunctor.obj P.X)).hom)) ≫
        dualHom (G.toFunctor.map (F.toFunctor.map P.p))) =
      G.toFunctor.map (F.toFunctor.map (dualHom P.p)) ≫
        (G.toFunctor.map (F.ξ P.X).hom ≫ (G.ξ (F.toFunctor.obj P.X)).hom)
    have hz : G.toFunctor.map (dualHom (F.toFunctor.map P.p)) ≫ (G.ξ (F.toFunctor.obj P.X)).hom ≫
        dualHom (G.toFunctor.map (F.toFunctor.map P.p)) =
          G.toFunctor.map (dualHom (F.toFunctor.map P.p)) ≫ (G.ξ (F.toFunctor.obj P.X)).hom := by
      rw [← Category.assoc, G.ξ_natural, Category.assoc, ← dualHom_comp, ← G.toFunctor.map_comp,
        ← F.toFunctor.map_comp, P.idem]
    have h1 : F.toFunctor.map (dualHom P.p) ≫ F.toFunctor.map (dualHom P.p) ≫ (F.ξ P.X).hom ≫
        dualHom (F.toFunctor.map P.p) = F.toFunctor.map (dualHom P.p) ≫ (F.ξ P.X).hom := by
      rw [← Category.assoc, ← F.toFunctor.map_comp, ← dualHom_comp, P.idem, ← Category.assoc,
        F.ξ_natural, Category.assoc, hid]
    simp only [Category.assoc]
    rw [hz, ← G.toFunctor.map_comp_assoc, ← G.toFunctor.map_comp_assoc,
      ← G.toFunctor.map_comp_assoc]
    simp only [Category.assoc]
    rw [h1]

/-- `(G ∘ F)_* = G_* ∘ F_*` on `L^p_k(A)`. -/
theorem Lp.map_comp (F : DualFunctor A A') (G : DualFunctor A' A'') (k : ℤ) :
    Lp.map (F.comp G) k = (Lp.map G k).comp (Lp.map F k) := by
  rw [Lp.map, LGroup.map_eq_of_unitaryIso (karCompIso F G), LGroup.map_comp]

end HSP
