import Mathlib
import HilbertSmithPaper.LTheory.Base.Groups.LGroupAdd
import HilbertSmithPaper.LTheory.Localization.Boundary.ImagePair
import HilbertSmithPaper.LTheory.Localization.Decorations.DecoratedLGroup
import HilbertSmithPaper.LTheory.Base.Groups.ProjectiveLGroup
import HilbertSmithPaper.LTheory.Localization.Decorations.SubcategorySum
import HilbertSmithPaper.LTheory.Base.Pairs.SumOfPairs
import HilbertSmithPaper.LTheory.Base.Pairs.PairTransport
import HilbertSmithPaper.LTheory.Base.Complexes.Functors.FunctorStructureSum
import HilbertSmithPaper.LTheory.Base.Complexes.Functors.PushId

/-!
# Sums of U-pairs

For strict `k`-dimensional `𝒰`-pairs `V` over `(P, π)` and `V'` over `(P', π')` there is a strict
`k`-dimensional `𝒰`-pair `V''` with `[q V''] = [q V] + [q V']` in `L^{im}_k(𝒜/𝒰)` and boundary
class `[P'', π''] = [P, π] + [P', π']` in `L^p_{k-1}(𝒰)`.

The sum `V ⊕ V'` of the pairs, transported along `i(P ⊕ P') ≅ iP ⊕ iP' ≅ C ⊕ C'`, is a `𝒰`-pair over
`(P ⊕ P', π ⊕ π')`; the canonical isomorphism `q(D ⊕ D') ≅ qD ⊕ qD'` carries its image structure
to `q_% δφ ⊕ q_% δφ'`, and sums in the full subcategory of decorated objects give the image class.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents

namespace HSP

universe v u

attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts

section Push

variable {V : Type*} [Category V] [Preadditive V] [Linear ℚ V] [HasFiniteBiproducts V]
  [DualCat V]

private lemma push_comp_apply {C D E : ChainComplex V ℤ} (f : C ⟶ D) (g : D ⟶ E) (n : ℤ)
    (φ : (StructureCx C).X n) :
    (StructureCx.push (f ≫ g)).f n φ = (StructureCx.push g).f n ((StructureCx.push f).f n φ) := by
  rw [StructureCx.push_comp]
  rfl

private lemma push_inv_hom {C D : ChainComplex V ℤ} (u : C ≅ D) (n : ℤ)
    (φ : (StructureCx C).X n) :
    (StructureCx.push u.inv).f n ((StructureCx.push u.hom).f n φ) = φ := by
  rw [← push_comp_apply, u.hom_inv_id, StructureCx.push_id]
  rfl

private lemma push_map_sum {X Y X' Y' : ChainComplex V ℤ} (g : X ⟶ X') (g' : Y ⟶ Y') (n : ℤ)
    (a : (StructureCx X).X n) (b : (StructureCx Y).X n) :
    (StructureCx.push (biprod.map g g')).f n (StructureCx.sum a b) =
      StructureCx.sum ((StructureCx.push g).f n a) ((StructureCx.push g').f n b) := by
  unfold StructureCx.sum
  rw [map_add, ← push_comp_apply, ← push_comp_apply, biprod.inl_map, biprod.inr_map,
    push_comp_apply, push_comp_apply]

private lemma iso_of_sigma_eq {k : ℤ} {C₀ C : ChainComplex V ℤ}
    {φ₀ : (StructureCx C₀).X k} {φ : (StructureCx C).X k}
    (h : (⟨C₀, φ₀⟩ : Σ C : ChainComplex V ℤ, (StructureCx C).X k) = ⟨C, φ⟩) :
    ∃ u : C ≅ C₀, (StructureCx.push u.hom).f k φ = φ₀ := by
  obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.mp h
  obtain rfl := eq_of_heq h
  exact ⟨Iso.refl _, by rw [Iso.refl_hom, StructureCx.push_id]; rfl⟩

end Push

variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A] {U : ObjectProperty A} [IsDualAdditive U]

/-- **Sums of U-pairs.** A `𝒰`-pair whose image class and boundary class are the sums. -/
theorem UPair.exists_add {k : ℤ} (V V' : UPair U k) :
    ∃ V'' : UPair U k, LGroup.mk V''.image = LGroup.mk V.image + LGroup.mk V'.image ∧
      (LGroup.mk V''.P : Lp U.FullSubcategory (k - 1)) = LGroup.mk V.P + LGroup.mk V'.P := by
  let i := (DualSubcategory.incl U).kar
  let Im := i.toFunctor.mapHomologicalComplex (ComplexShape.down ℤ)
  obtain ⟨w, hw⟩ := SymPoincare.exists_sum_iso V.P V'.P
  obtain ⟨a, ha⟩ := iso_of_sigma_eq V.boundary_eq
  obtain ⟨a', ha'⟩ := iso_of_sigma_eq V'.boundary_eq
  obtain ⟨S, hS⟩ := SymPair.sum V.V V'.V
  obtain ⟨s, hs⟩ := iso_of_sigma_eq (congrArg (fun d : SymPair.Data (Karoubi A) (k - 1) k =>
    (⟨d.1, d.2.2.2.2⟩ : Σ C : ChainComplex (Karoubi A) ℤ, (StructureCx C).X (k - 1))) hS)
  let P'' := V.P.sum V'.P
  let u : i.mapCx P''.C ≅ S.C :=
    Im.mapIso w.symm ≪≫ Im.mapBiprod V.P.C V'.P.C ≪≫ biprod.mapIso a a' ≪≫ s
  have hu : (StructureCx.push u.hom).f (k - 1) (i.mapStructure P''.C (k - 1) P''.φ) = S.φ := by
    have h1 : (StructureCx.push (Im.map w.inv)).f (k - 1) (i.mapStructure P''.C (k - 1) P''.φ) =
        i.mapStructure _ (k - 1) (StructureCx.sum V.P.φ V'.P.φ) := by
      rw [← DualFunctor.mapStructure_pushforward, ← hw, push_inv_hom]
    have h2 : (StructureCx.push (Im.mapBiprod V.P.C V'.P.C).hom).f (k - 1)
        (i.mapStructure _ (k - 1) (StructureCx.sum V.P.φ V'.P.φ)) =
        StructureCx.sum (i.mapStructure _ (k - 1) V.P.φ) (i.mapStructure _ (k - 1) V'.P.φ) := by
      rw [← DualFunctor.mapStructure_sum, ← push_comp_apply, Iso.inv_hom_id, StructureCx.push_id]
      rfl
    change (StructureCx.push (Im.map w.inv ≫ (Im.mapBiprod V.P.C V'.P.C).hom ≫
      biprod.map a.hom a'.hom ≫ s.hom)).f (k - 1) _ = _
    rw [push_comp_apply, h1, push_comp_apply, h2, push_comp_apply, push_map_sum, ha, ha', hs]
  obtain ⟨W, hW⟩ := SymPair.transport S u _ hu 1
  have hbd : (⟨W.C, W.φ⟩ : Σ C : ChainComplex (Karoubi A) ℤ, (StructureCx C).X (k - 1)) =
      ⟨i.mapCx P''.C, i.mapStructure P''.C (k - 1) P''.φ⟩ := by
    have := congrArg (fun d : SymPair.Data (Karoubi A) (k - 1) k =>
      (⟨d.1, d.2.2.2.2⟩ : Σ C : ChainComplex (Karoubi A) ℤ, (StructureCx C).X (k - 1))) hW
    simpa only [one_smul] using this
  refine ⟨⟨P'', W, hbd⟩, ?_, (LGroup.mk_add _ _).symm⟩
  -- the image classes
  have hD : (⟨W.D, W.δφ⟩ : Σ D : ChainComplex (Karoubi A) ℤ, (StructureCx D).X k) =
      ⟨V.V.D ⊞ V'.V.D, StructureCx.sum V.V.δφ V'.V.δφ⟩ := by
    have h1 := congrArg (fun d : SymPair.Data (Karoubi A) (k - 1) k =>
      (⟨d.2.1, d.2.2.2.1⟩ : Σ D : ChainComplex (Karoubi A) ℤ, (StructureCx D).X k)) hW
    have h2 := congrArg (fun d : SymPair.Data (Karoubi A) (k - 1) k =>
      (⟨d.2.1, d.2.2.2.1⟩ : Σ D : ChainComplex (Karoubi A) ℤ, (StructureCx D).X k)) hS
    simp only [one_smul] at h1
    exact h1.trans h2
  obtain ⟨t, ht⟩ := iso_of_sigma_eq hD.symm
  let Q := (FiltQuot.q U).kar
  let Qm := Q.toFunctor.mapHomologicalComplex (ComplexShape.down ℤ)
  let ui : Q.mapCx W.D ≅ Q.mapCx V.V.D ⊞ Q.mapCx V'.V.D := Qm.mapIso t ≪≫ Qm.mapBiprod _ _
  have hinv : (StructureCx.push ui.inv).f k
      (StructureCx.sum (Q.mapStructure _ k V.V.δφ) (Q.mapStructure _ k V'.V.δφ)) =
      Q.mapStructure W.D k W.δφ := by
    have : ui.inv = (Qm.mapBiprod V.V.D V'.V.D).inv ≫ Qm.map t.inv := rfl
    rw [this, push_comp_apply, DualFunctor.mapStructure_sum,
      ← DualFunctor.mapStructure_pushforward, ← ht, push_inv_hom]
  have hui : (StructureCx.push ui.hom).f k (Q.mapStructure W.D k W.δφ) =
      StructureCx.sum (Q.mapStructure _ k V.V.δφ) (Q.mapStructure _ k V'.V.δφ) := by
    rw [← hinv, ← push_comp_apply, ui.inv_hom_id, StructureCx.push_id]
    rfl
  let V'' : UPair U k := ⟨P'', W, hbd⟩
  refine SymPoincare.mk_eq_add_of_sumIso (IsDecorated U) V''.image V.image V'.image ui ?_
  rw [UPair.incl_mapStructure_image, UPair.incl_mapStructure_image, UPair.incl_mapStructure_image]
  exact hui

end HSP
