import HilbertSmithPaper.LTheory.Base.Pairs.FunctorPair
import HilbertSmithPaper.LTheory.Base.Complexes.FunctorPush
import HilbertSmithPaper.LTheory.Base.Pairs.IsoCobordism
import HilbertSmithPaper.LTheory.Base.Pairs.TransportCobordism
import HilbertSmithPaper.LTheory.Base.Pairs.PoincareSum

/-!
# Duality functors on cobordism classes

The image under a duality functor of cobordant strict symmetric Poincaré complexes are cobordant,
and the image of a sum is cobordant to the sum of the images.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

open DualCat

universe v₁ v₂ u₁ u₂

variable {B : Type u₁} [Category.{v₁} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B]
  {B' : Type u₂} [Category.{v₂} B'] [Preadditive B'] [Linear ℚ B'] [HasFiniteBiproducts B']
  [DualCat B']

namespace StructureCx

private lemma push_comp_apply {C D E : ChainComplex B ℤ} (g : C ⟶ D) (h : D ⟶ E) {k : ℤ}
    (a : (StructureCx C).X k) :
    (push (g ≫ h)).f k a = (push h).f k ((push g).f k a) := by
  rw [push_comp]
  rfl

private lemma push_sum {X Y Z : ChainComplex B ℤ} (g : X ⊞ Y ⟶ Z) {k : ℤ}
    (a : (StructureCx X).X k) (b : (StructureCx Y).X k) :
    (push g).f k (StructureCx.sum a b) = (push (biprod.inl ≫ g)).f k a + (push (biprod.inr ≫ g)).f k b := by
  rw [StructureCx.sum, map_add, push_comp_apply, push_comp_apply]

private lemma push_inv_hom {C D : ChainComplex B ℤ} (u : C ≅ D) {k : ℤ}
    (a : (StructureCx C).X k) : (push u.inv).f k ((push u.hom).f k a) = a := by
  rw [← push_comp_apply, u.hom_inv_id, push_id]
  rfl

private lemma exists_iso_of_sigma_eq {k : ℤ} {C₀ C : ChainComplex B ℤ} {φ₀ : (StructureCx C₀).X k}
    {φ : (StructureCx C).X k}
    (h : (⟨C₀, φ₀⟩ : Σ C : ChainComplex B ℤ, (StructureCx C).X k) = ⟨C, φ⟩) :
    ∃ u : C ≅ C₀, (push u.hom).f k φ = φ₀ := by
  obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.mp h
  obtain rfl := eq_of_heq h
  exact ⟨Iso.refl _, by rw [Iso.refl_hom, push_id]; rfl⟩

end StructureCx

open StructureCx

namespace InducedMapLaws

open StructureCx

/-- `F C ⊞ F C' ≅ F (C ⊞ C')` for the additive functor `F`. -/
private noncomputable def mapBiprodIso (F : DualFunctor B B') (X Y : ChainComplex B ℤ) :
    F.mapCx X ⊞ F.mapCx Y ≅ F.mapCx (X ⊞ Y) where
  hom := biprod.desc ((F.toFunctor.mapHomologicalComplex _).map biprod.inl)
    ((F.toFunctor.mapHomologicalComplex _).map biprod.inr)
  inv := biprod.lift ((F.toFunctor.mapHomologicalComplex _).map biprod.fst)
    ((F.toFunctor.mapHomologicalComplex _).map biprod.snd)
  hom_inv_id := by
    apply biprod.hom_ext' <;> apply biprod.hom_ext <;> simp [← Functor.map_comp]
  inv_hom_id := by
    rw [biprod.lift_desc, ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
      ← CategoryTheory.Functor.map_add, biprod.total, CategoryTheory.Functor.map_id]

private lemma push_mapBiprodIso (F : DualFunctor B B') (X Y : ChainComplex B ℤ) {k : ℤ}
    (a : (StructureCx X).X k) (b : (StructureCx Y).X k) :
    (push (mapBiprodIso F X Y).hom).f k (StructureCx.sum (F.mapStructure X k a) (F.mapStructure Y k b)) =
      F.mapStructure (X ⊞ Y) k (StructureCx.sum a b) := by
  rw [push_sum]
  simp only [mapBiprodIso, biprod.inl_desc, biprod.inr_desc]
  rw [← F.mapStructure_pushforward, ← F.mapStructure_pushforward, StructureCx.sum, map_add]

end InducedMapLaws

open InducedMapLaws StructureCx in
/-- A duality functor preserves cobordism, and preserves sums up to cobordism. -/
theorem SymPoincare.map_cobordant (F : DualFunctor B B') {k : ℤ} :
    (∀ x y : SymPoincare B k, Cobordant x y → Cobordant (x.map F) (y.map F)) ∧
    (∀ x y : SymPoincare B k, Cobordant ((x.sum y).map F) ((x.map F).sum (y.map F))) := by
  refine ⟨?_, ?_⟩
  · rintro x y ⟨W, hW⟩
    obtain ⟨u, hu⟩ := exists_iso_of_sigma_eq hW
    refine Cobordant.of_transport (x.map F) (y.map F) (W.map F)
      (mapBiprodIso F x.C y.C ≪≫ (F.toFunctor.mapHomologicalComplex _).mapIso u)
      (StructureCx.sum (x.map F).φ (-(y.map F).φ)) ?_ 1 (one_smul _ _)
    change (push ((mapBiprodIso F x.C y.C).hom ≫
      (F.toFunctor.mapHomologicalComplex _).map u.hom)).f k
        (StructureCx.sum (F.mapStructure x.C k x.φ) (-F.mapStructure y.C k y.φ)) =
          F.mapStructure W.C k W.φ
    rw [push_comp_apply, ← map_neg, push_mapBiprodIso, ← F.mapStructure_pushforward, hu]
  · intro x y
    obtain ⟨s, hs⟩ := SymPoincare.exists_sum_iso x y
    obtain ⟨s', hs'⟩ : ∃ u : F.mapCx x.C ⊞ F.mapCx y.C ≅ ((x.map F).sum (y.map F)).C,
        (push u.hom).f k (StructureCx.sum (F.mapStructure x.C k x.φ) (F.mapStructure y.C k y.φ)) =
          ((x.map F).sum (y.map F)).φ :=
      SymPoincare.exists_sum_iso (x.map F) (y.map F)
    refine Cobordant.of_iso _ _ ((F.toFunctor.mapHomologicalComplex _).mapIso s.symm ≪≫
      (mapBiprodIso F x.C y.C).symm ≪≫ s') ?_
    change (push ((F.toFunctor.mapHomologicalComplex _).map s.inv ≫
      (mapBiprodIso F x.C y.C).inv ≫ s'.hom)).f k
        (F.mapStructure (x.sum y).C k (x.sum y).φ) = _
    rw [push_comp_apply, push_comp_apply, ← hs, ← F.mapStructure_pushforward, push_inv_hom, ← push_mapBiprodIso, push_inv_hom]
    exact hs'

end HSP
