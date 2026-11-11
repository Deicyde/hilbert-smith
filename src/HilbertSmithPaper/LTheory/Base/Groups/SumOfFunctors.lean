import HilbertSmithPaper.LTheory.Base.Categories.Sums.DualityFunctorSum
import HilbertSmithPaper.LTheory.Base.Complexes.Functors.PushComp
import HilbertSmithPaper.LTheory.Base.Groups.InducedMap
import HilbertSmithPaper.LTheory.Base.Groups.LGroupAdd
import HilbertSmithPaper.LTheory.Base.Pairs.IsoCobordism
import HilbertSmithPaper.LTheory.Base.Pairs.PoincareSum

/-!
# Sums of functors

For duality functors `F, G : B → B'`, `(F ⊕ G)_* = F_* + G_*` on `L_k(B)`: the image of `(C, φ)`
under `F ⊕ G` is isomorphic to `(F C ⊕ G C, F_% φ ⊕ G_% φ)`.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

open DualCat StructureCx

universe v₁ v₂ u₁ u₂

variable {B : Type u₁} [Category.{v₁} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B]
  {B' : Type u₂} [Category.{v₂} B'] [Preadditive B'] [Linear ℚ B'] [HasFiniteBiproducts B']
  [DualCat B']

namespace SumOfFunctors

variable (F G : DualFunctor B B') (C : ChainComplex B ℤ)

/-- The inclusion `F C → (F ⊕ G) C`. -/
private noncomputable def incl₁ : F.mapCx C ⟶ (F.biprod G).mapCx C where
  f r := (biprod.inl : F.toFunctor.obj (C.X r) ⟶ F.toFunctor.obj (C.X r) ⊞ G.toFunctor.obj (C.X r))
  comm' i j _ := by
    change biprod.inl ≫ biprod.map (F.toFunctor.map (C.d i j)) (G.toFunctor.map (C.d i j)) =
      F.toFunctor.map (C.d i j) ≫ biprod.inl
    rw [biprod.inl_map]

/-- The inclusion `G C → (F ⊕ G) C`. -/
private noncomputable def incl₂ : G.mapCx C ⟶ (F.biprod G).mapCx C where
  f r := (biprod.inr : G.toFunctor.obj (C.X r) ⟶ F.toFunctor.obj (C.X r) ⊞ G.toFunctor.obj (C.X r))
  comm' i j _ := by
    change biprod.inr ≫ biprod.map (F.toFunctor.map (C.d i j)) (G.toFunctor.map (C.d i j)) =
      G.toFunctor.map (C.d i j) ≫ biprod.inr
    rw [biprod.inr_map]

/-- The projection `(F ⊕ G) C → F C`. -/
private noncomputable def proj₁ : (F.biprod G).mapCx C ⟶ F.mapCx C where
  f r := (biprod.fst : F.toFunctor.obj (C.X r) ⊞ G.toFunctor.obj (C.X r) ⟶ F.toFunctor.obj (C.X r))
  comm' i j _ := by
    change biprod.fst ≫ F.toFunctor.map (C.d i j) =
      biprod.map (F.toFunctor.map (C.d i j)) (G.toFunctor.map (C.d i j)) ≫ biprod.fst
    rw [biprod.map_fst]

/-- The projection `(F ⊕ G) C → G C`. -/
private noncomputable def proj₂ : (F.biprod G).mapCx C ⟶ G.mapCx C where
  f r := (biprod.snd : F.toFunctor.obj (C.X r) ⊞ G.toFunctor.obj (C.X r) ⟶ G.toFunctor.obj (C.X r))
  comm' i j _ := by
    change biprod.snd ≫ G.toFunctor.map (C.d i j) =
      biprod.map (F.toFunctor.map (C.d i j)) (G.toFunctor.map (C.d i j)) ≫ biprod.snd
    rw [biprod.map_snd]

/-- `F C ⊕ G C ≅ (F ⊕ G) C`. -/
private noncomputable def sumIso : F.mapCx C ⊞ G.mapCx C ≅ (F.biprod G).mapCx C where
  hom := biprod.desc (incl₁ F G C) (incl₂ F G C)
  inv := biprod.lift (proj₁ F G C) (proj₂ F G C)
  hom_inv_id := by
    apply biprod.hom_ext' <;> apply biprod.hom_ext <;>
      simp only [biprod.inl_desc_assoc, biprod.inr_desc_assoc, biprod.lift_fst, biprod.lift_snd,
        Category.assoc, biprod.inl_fst, biprod.inl_snd, biprod.inr_fst, biprod.inr_snd,
        Category.comp_id] <;>
      ext r <;>
      simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f, HomologicalComplex.zero_f,
        incl₁, incl₂, proj₁, proj₂] <;>
      first | exact biprod.inl_fst | exact biprod.inl_snd | exact biprod.inr_fst |
        exact biprod.inr_snd
  inv_hom_id := by
    rw [biprod.lift_desc]
    ext r
    simp only [HomologicalComplex.add_f_apply, HomologicalComplex.comp_f, HomologicalComplex.id_f]
    exact biprod.total

private lemma push_comp_apply {X Y Z : ChainComplex B' ℤ} (g : X ⟶ Y) (h : Y ⟶ Z) {k : ℤ}
    (a : (StructureCx X).X k) :
    (push (g ≫ h)).f k a = (push h).f k ((push g).f k a) := by
  rw [push_comp]
  rfl

private lemma push_inv_hom {X Y : ChainComplex B' ℤ} (u : X ≅ Y) {k : ℤ}
    (a : (StructureCx X).X k) : (push u.inv).f k ((push u.hom).f k a) = a := by
  rw [← push_comp_apply, u.hom_inv_id, push_id]
  rfl

/-- `F C ⊕ G C ≅ (F ⊕ G) C` carries `F_% φ ⊕ G_% φ` to `(F ⊕ G)_% φ`. -/
private lemma push_sumIso {k : ℤ} (φ : (StructureCx C).X k) :
    (push (sumIso F G C).hom).f k (StructureCx.sum (F.mapStructure C k φ) (G.mapStructure C k φ)) =
      (F.biprod G).mapStructure C k φ := by
  rw [StructureCx.sum, map_add, ← push_comp_apply, ← push_comp_apply]
  simp only [sumIso, biprod.inl_desc, biprod.inr_desc]
  funext ⟨⟨p, q⟩, h⟩
  change dualHom (biprod.inl : F.toFunctor.obj (C.X q) ⟶ _ ⊞ G.toFunctor.obj (C.X q)) ≫
      ((F.ξ (C.X q)).inv ≫ F.toFunctor.map (φ ⟨(p, q), h⟩)) ≫ biprod.inl +
    dualHom (biprod.inr : G.toFunctor.obj (C.X q) ⟶ F.toFunctor.obj (C.X q) ⊞ _) ≫
      ((G.ξ (C.X q)).inv ≫ G.toFunctor.map (φ ⟨(p, q), h⟩)) ≫ biprod.inr =
    (biprod.lift (dualHom biprod.inl) (dualHom biprod.inr) ≫
      biprod.map (F.ξ (C.X q)).inv (G.ξ (C.X q)).inv) ≫
      biprod.map (F.toFunctor.map (φ ⟨(p, q), h⟩)) (G.toFunctor.map (φ ⟨(p, q), h⟩))
  apply biprod.hom_ext <;> simp

end SumOfFunctors

open SumOfFunctors in
/-- **Sums of functors.** `(F ⊕ G)_* = F_* + G_*` on `L_k(B)`. -/
theorem LGroup.map_biprod (F G : DualFunctor B B') (k : ℤ) :
    LGroup.map (F.biprod G) k = LGroup.map F k + LGroup.map G k := by
  refine AddMonoidHom.ext fun a => Quotient.inductionOn a fun x => ?_
  change LGroup.mk (x.map (F.biprod G)) = LGroup.mk (x.map F) + LGroup.mk (x.map G)
  rw [LGroup.mk_add]
  refine Quotient.sound (Setoid.symm ?_)
  obtain ⟨s, hs⟩ := SymPoincare.exists_sum_iso (x.map F) (x.map G)
  refine Cobordant.of_iso _ _ (s.symm ≪≫ sumIso F G x.C) ?_
  change (push (s.inv ≫ (sumIso F G x.C).hom)).f k ((x.map F).sum (x.map G)).φ =
    (F.biprod G).mapStructure x.C k x.φ
  erw [push_comp_apply, ← hs, push_inv_hom]
  exact push_sumIso F G x.C x.φ

end HSP
