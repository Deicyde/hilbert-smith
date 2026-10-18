import Mathlib

namespace HilbertSmith

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- A duality on an additive category: a contravariant additive
endofunctor with a biduality isomorphism. -/
structure Duality (C : Type u) [Category.{v} C] [Preadditive C] where
  /-- The duality functor `Cᵒᵖ ⥤ C`. -/
  D : Cᵒᵖ ⥤ C
  /-- The biduality comparison `Id ≅ D ∘ Dᵒᵖ`. -/
  biduality : 𝟭 C ≅ opOp C ⋙ D.op ⋙ D

variable (d : Duality C) [d.D.Additive]

/-- The transpose of `α : X ⟶ DX`: biduality followed by `D` applied
to `α`. -/
def Duality.transpose {X : C} (α : X ⟶ d.D.obj (op X)) :
    X ⟶ d.D.obj (op X) :=
  d.biduality.hom.app X ≫ d.D.map α.op

/-- A symmetric form: a morphism equal to its own transpose. -/
def Duality.IsSymmetric {X : C} (α : X ⟶ d.D.obj (op X)) : Prop :=
  α = d.transpose α

variable [HasBinaryBiproducts C]

/-- The canonical map `D(X ⊞ Y) ⟶ DX ⊞ DY`. -/
noncomputable def Duality.dualBiprodHom (X Y : C) :
    d.D.obj (op (X ⊞ Y)) ⟶ d.D.obj (op X) ⊞ d.D.obj (op Y) :=
  biprod.lift (d.D.map biprod.inl.op) (d.D.map biprod.inr.op)

/-- The canonical map `DX ⊞ DY ⟶ D(X ⊞ Y)`. -/
noncomputable def Duality.dualBiprodInv (X Y : C) :
    d.D.obj (op X) ⊞ d.D.obj (op Y) ⟶ d.D.obj (op (X ⊞ Y)) :=
  biprod.desc (d.D.map biprod.fst.op) (d.D.map biprod.snd.op)

/-- A duality preserves binary biproducts. -/
noncomputable def Duality.dualBiprodIso (X Y : C) :
    d.D.obj (op (X ⊞ Y)) ≅ d.D.obj (op X) ⊞ d.D.obj (op Y) where
  hom := d.dualBiprodHom X Y
  inv := d.dualBiprodInv X Y
  hom_inv_id := by
    unfold dualBiprodHom dualBiprodInv
    rw [biprod.lift_desc, ← d.D.map_comp, ← d.D.map_comp, ← op_comp, ← op_comp,
      ← d.D.map_add, ← op_add]
    have h : biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr = 𝟙 (X ⊞ Y) := by
      apply biprod.hom_ext'
      · simp
      · simp
    rw [h]
    simp
  inv_hom_id := by
    unfold dualBiprodHom dualBiprodInv
    apply biprod.hom_ext'
    · rw [← Category.assoc, biprod.inl_desc]
      apply biprod.hom_ext
      · rw [Category.assoc, biprod.lift_fst, ← d.D.map_comp, ← op_comp,
          biprod.inl_fst]
        simp
      · rw [Category.assoc, biprod.lift_snd, ← d.D.map_comp, ← op_comp,
          biprod.inr_fst]
        simp
    · rw [← Category.assoc, biprod.inr_desc]
      apply biprod.hom_ext
      · rw [Category.assoc, biprod.lift_fst, ← d.D.map_comp, ← op_comp,
          biprod.inl_snd]
        simp
      · rw [Category.assoc, biprod.lift_snd, ← d.D.map_comp, ← op_comp,
          biprod.inr_snd]
        simp

/-- Precomposing a lift distributes over the legs. -/
theorem comp_lift {V W X Y : C} (k : V ⟶ W) (f : W ⟶ X) (g : W ⟶ Y) :
    k ≫ biprod.lift f g = biprod.lift (k ≫ f) (k ≫ g) := by
  apply biprod.hom_ext <;> simp [Category.assoc]

/-- Postcomposing a lift with a map distributes over the legs. -/
theorem lift_map {W X Y X' Y' : C} (f : W ⟶ X) (g : W ⟶ Y)
    (h : X ⟶ X') (k : Y ⟶ Y') :
    biprod.lift f g ≫ biprod.map h k =
      biprod.lift (f ≫ h) (g ≫ k) := by
  apply biprod.hom_ext <;> simp [Category.assoc]

/-- The comparison map is natural with respect to `D` applied to a map. -/
theorem Duality.map_hom_naturality {X Y X' Y' : C}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    d.D.map (biprod.map f g).op ≫ (d.dualBiprodIso X Y).hom =
      (d.dualBiprodIso X' Y').hom ≫
        biprod.map (d.D.map f.op) (d.D.map g.op) := by
  show d.D.map (biprod.map f g).op ≫ d.dualBiprodHom X Y =
    d.dualBiprodHom X' Y' ≫ biprod.map (d.D.map f.op) (d.D.map g.op)
  unfold dualBiprodHom
  apply biprod.hom_ext
  · rw [Category.assoc, Category.assoc, biprod.lift_fst, biprod.map_fst,
      ← Category.assoc, biprod.lift_fst, ← d.D.map_comp, ← op_comp,
      biprod.inl_map, op_comp, d.D.map_comp]
  · rw [Category.assoc, Category.assoc, biprod.lift_snd, biprod.map_snd,
      ← Category.assoc, biprod.lift_snd, ← d.D.map_comp, ← op_comp,
      biprod.inr_map, op_comp, d.D.map_comp]

/-- The solved form: `D` applied to a map, conjugated by the comparison. -/
theorem Duality.map_map_op {X Y X' Y' : C}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    d.D.map (biprod.map f g).op =
      (d.dualBiprodIso X' Y').hom ≫
        biprod.map (d.D.map f.op) (d.D.map g.op) ≫
        (d.dualBiprodIso X Y).inv := by
  calc d.D.map (biprod.map f g).op
      = (d.D.map (biprod.map f g).op ≫
          (d.dualBiprodIso X Y).hom) ≫
          (d.dualBiprodIso X Y).inv := by
        rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    _ = _ := by rw [d.map_hom_naturality f g, Category.assoc]

/-- `D` applied to the inverse comparison, followed by the comparison. -/
theorem Duality.inv_map_hom {X Y : C} :
    d.D.map (d.dualBiprodIso X Y).inv.op ≫
      (d.dualBiprodIso (d.D.obj (op X)) (d.D.obj (op Y))).hom =
      biprod.lift ((opOp C ⋙ d.D.op ⋙ d.D).map biprod.fst)
        ((opOp C ⋙ d.D.op ⋙ d.D).map biprod.snd) := by
  have h1 : (d.D.map (d.dualBiprodIso X Y).inv.op ≫
      (d.dualBiprodIso (d.D.obj (op X)) (d.D.obj (op Y))).hom) ≫ biprod.fst =
      (opOp C ⋙ d.D.op ⋙ d.D).map biprod.fst := by
    show (d.D.map (d.dualBiprodInv X Y).op ≫ d.dualBiprodHom _ _) ≫ _ = _
    unfold dualBiprodInv dualBiprodHom
    rw [Category.assoc, biprod.lift_fst, ← d.D.map_comp, ← op_comp,
      biprod.inl_desc, Functor.comp_map, Functor.comp_map, opOp_map,
      Functor.op_map, Quiver.Hom.unop_op]
  have h2 : (d.D.map (d.dualBiprodIso X Y).inv.op ≫
      (d.dualBiprodIso (d.D.obj (op X)) (d.D.obj (op Y))).hom) ≫ biprod.snd =
      (opOp C ⋙ d.D.op ⋙ d.D).map biprod.snd := by
    show (d.D.map (d.dualBiprodInv X Y).op ≫ d.dualBiprodHom _ _) ≫ _ = _
    unfold dualBiprodInv dualBiprodHom
    rw [Category.assoc, biprod.lift_snd, ← d.D.map_comp, ← op_comp,
      biprod.inr_desc, Functor.comp_map, Functor.comp_map, opOp_map,
      Functor.op_map, Quiver.Hom.unop_op]
  apply biprod.hom_ext
  · rw [h1]
    exact (biprod.lift_fst _ _).symm
  · rw [h2]
    exact (biprod.lift_snd _ _).symm

/-- The orthogonal sum of two forms. -/
noncomputable def Duality.orthSum {X Y : C}
    (α : X ⟶ d.D.obj (op X)) (β : Y ⟶ d.D.obj (op Y)) :
    (X ⊞ Y) ⟶ d.D.obj (op (X ⊞ Y)) :=
  biprod.map α β ≫ (d.dualBiprodIso X Y).inv

/-- Orthogonal sums of symmetric forms are symmetric. -/
theorem Duality.orthSum_symm {X Y : C}
    {α : X ⟶ d.D.obj (op X)} {β : Y ⟶ d.D.obj (op Y)}
    (hα : d.IsSymmetric α) (hβ : d.IsSymmetric β) :
    d.IsSymmetric (d.orthSum α β) := by
  unfold Duality.IsSymmetric Duality.transpose at hα hβ ⊢
  unfold Duality.orthSum at ⊢
  rw [op_comp, d.D.map_comp, d.map_map_op]
  simp only [← Category.assoc]
  have Kgen : ∀ (k : X ⊞ Y ⟶
      d.D.obj (op (d.D.obj (op (X ⊞ Y))))),
      (k ≫ d.D.map (d.dualBiprodIso X Y).inv.op) ≫
        (d.dualBiprodIso (d.D.obj (op X)) (d.D.obj (op Y))).hom =
      k ≫ biprod.lift ((opOp C ⋙ d.D.op ⋙ d.D).map biprod.fst)
        ((opOp C ⋙ d.D.op ⋙ d.D).map biprod.snd) := by
    intro k
    rw [Category.assoc, d.inv_map_hom]
  rw [Kgen]
  have nat_fst : d.biduality.hom.app (X ⊞ Y) ≫
      (opOp C ⋙ d.D.op ⋙ d.D).map biprod.fst =
      (biprod.fst : X ⊞ Y ⟶ X) ≫ d.biduality.hom.app X := by
    have h := d.biduality.hom.naturality (biprod.fst : X ⊞ Y ⟶ X)
    simpa using h.symm
  have nat_snd : d.biduality.hom.app (X ⊞ Y) ≫
      (opOp C ⋙ d.D.op ⋙ d.D).map biprod.snd =
      (biprod.snd : X ⊞ Y ⟶ Y) ≫ d.biduality.hom.app Y := by
    have h := d.biduality.hom.naturality (biprod.snd : X ⊞ Y ⟶ Y)
    simpa using h.symm
  have map_eq_lift : biprod.map α β =
      biprod.lift (biprod.fst ≫ α) (biprod.snd ≫ β) := by
    apply biprod.hom_ext <;> simp
  have e1 : ((biprod.fst : X ⊞ Y ⟶ X) ≫ d.biduality.hom.app X) ≫ d.D.map α.op =
      biprod.fst ≫ α := by
    rw [Category.assoc, ← hα]
  have e2 : ((biprod.snd : X ⊞ Y ⟶ Y) ≫ d.biduality.hom.app Y) ≫ d.D.map β.op =
      biprod.snd ≫ β := by
    rw [Category.assoc, ← hβ]
  rw [comp_lift, nat_fst, nat_snd, lift_map, e1, e2, ← map_eq_lift]

end HilbertSmith
