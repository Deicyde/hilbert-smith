import Mathlib
import HilbertSmith.SymmetricForms

namespace HilbertSmith

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

variable {C : Type u} [Category.{v} C] [Preadditive C]

variable (d : Duality C) [d.D.Additive]

/-- An involutive duality: dualized biduality cancels biduality. -/
def Duality.IsInvolutive : Prop :=
  ∀ X : C, d.biduality.hom.app (d.D.obj (op X)) ≫
    d.D.map (d.biduality.hom.app X).op = 𝟙 (d.D.obj (op X))

/-- Applying the biduality functor is applying `D` twice. -/
theorem Duality.biduality_map (d : Duality C) {X Y : C} (f : X ⟶ Y) :
    (opOp C ⋙ d.D.op ⋙ d.D).map f = d.D.map (d.D.map f.op).op := by
  rw [Functor.comp_map, Functor.comp_map, opOp_map, Functor.op_map,
    Quiver.Hom.unop_op]

/-- For an involutive duality, the transpose is involutive. -/
theorem Duality.transpose_transpose (d : Duality C) (h : d.IsInvolutive)
    {X : C} (α : X ⟶ d.D.obj (op X)) :
    d.transpose (d.transpose α) = α := by
  have nat : d.biduality.hom.app X ≫ (opOp C ⋙ d.D.op ⋙ d.D).map α =
      α ≫ d.biduality.hom.app (d.D.obj (op X)) := by
    have h' := d.biduality.hom.naturality α
    simpa using h'.symm
  have hX := h X
  unfold Duality.transpose
  rw [op_comp, d.D.map_comp, ← d.biduality_map, ← Category.assoc, nat,
    Category.assoc, hX, Category.comp_id]

/-- The transpose is additive. -/
theorem Duality.transpose_add {X : C} (α β : X ⟶ d.D.obj (op X)) :
    d.transpose (α + β) = d.transpose α + d.transpose β := by
  unfold Duality.transpose
  rw [op_add, d.D.map_add, Preadditive.comp_add]

/-- The transpose of zero is zero. -/
theorem Duality.transpose_zero {X : C} :
    d.transpose (0 : X ⟶ d.D.obj (op X)) = 0 := by
  have h0 := d.transpose_add (0 : X ⟶ d.D.obj (op X)) 0
  rw [add_zero] at h0
  have h1 := congrArg
    (fun x => x + (-d.transpose (0 : X ⟶ d.D.obj (op X)))) h0
  simpa using h1.symm

variable [HasBinaryBiproducts C]

/-- Composition of biproduct maps. -/
theorem map_comp_map {X Y X' Y' X'' Y'' : C} (f : X ⟶ X') (g : Y ⟶ Y')
    (h : X' ⟶ X'') (k : Y' ⟶ Y'') :
    biprod.map f g ≫ biprod.map h k = biprod.map (f ≫ h) (g ≫ k) := by
  apply biprod.hom_ext <;> simp [Category.assoc]

/-- The transpose of an orthogonal sum is the orthogonal sum of the
transposes. -/
theorem Duality.transpose_orthSum {X Y : C}
    {α : X ⟶ d.D.obj (op X)} {β : Y ⟶ d.D.obj (op Y)} :
    d.transpose (d.orthSum α β) =
      d.orthSum (d.transpose α) (d.transpose β) := by
  have nat_fst : d.biduality.hom.app (X ⊞ Y) ≫
      (opOp C ⋙ d.D.op ⋙ d.D).map (biprod.fst : X ⊞ Y ⟶ X) =
      (biprod.fst : X ⊞ Y ⟶ X) ≫ d.biduality.hom.app X := by
    have h := d.biduality.hom.naturality (biprod.fst : X ⊞ Y ⟶ X)
    simpa using h.symm
  have nat_snd : d.biduality.hom.app (X ⊞ Y) ≫
      (opOp C ⋙ d.D.op ⋙ d.D).map (biprod.snd : X ⊞ Y ⟶ Y) =
      (biprod.snd : X ⊞ Y ⟶ Y) ≫ d.biduality.hom.app Y := by
    have h := d.biduality.hom.naturality (biprod.snd : X ⊞ Y ⟶ Y)
    simpa using h.symm
  have Kgen : ∀ (k : X ⊞ Y ⟶
      d.D.obj (op (d.D.obj (op (X ⊞ Y))))),
      (k ≫ d.D.map (d.dualBiprodIso X Y).inv.op) ≫
        (d.dualBiprodIso (d.D.obj (op X)) (d.D.obj (op Y))).hom =
      k ≫ biprod.lift ((opOp C ⋙ d.D.op ⋙ d.D).map biprod.fst)
        ((opOp C ⋙ d.D.op ⋙ d.D).map biprod.snd) := by
    intro k
    rw [Category.assoc, d.inv_map_hom]
  have e1 : ((biprod.fst : X ⊞ Y ⟶ X) ≫ d.biduality.hom.app X) ≫
      d.D.map α.op =
      biprod.fst ≫ (d.biduality.hom.app X ≫ d.D.map α.op) :=
    Category.assoc _ _ _
  have e2 : ((biprod.snd : X ⊞ Y ⟶ Y) ≫ d.biduality.hom.app Y) ≫
      d.D.map β.op =
      biprod.snd ≫ (d.biduality.hom.app Y ≫ d.D.map β.op) :=
    Category.assoc _ _ _
  unfold Duality.transpose Duality.orthSum
  rw [op_comp, d.D.map_comp, d.map_map_op]
  simp only [← Category.assoc]
  rw [Kgen, comp_lift, nat_fst, nat_snd, lift_map, e1, e2]
  congr 1
  apply biprod.hom_ext
  · rw [biprod.lift_fst, biprod.map_fst]; try rfl
  · rw [biprod.lift_snd, biprod.map_snd]; try rfl

end HilbertSmith
