import HilbertSmithPaper.LTheory.Base.Groups.LGroup
import HilbertSmithPaper.LTheory.Base.Groups.LGroupAddLaws

/-!
# Group structure on L

`L_k(B)` is an abelian group with `[C, φ] + [C', φ'] = [C ⊞ C', φ ⊕ φ']`, zero `[0, 0]` and
negation `-[C, φ] = [C, -φ]`. The operations are well defined and satisfy the group laws by
`cobordant_sum_laws`.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

universe v u

variable {B : Type u} [Category.{v} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B]

namespace LGroup

private lemma mk_eq_mk {k : ℤ} {x y : SymPoincare B k} (h : Cobordant x y) :
    (LGroup.mk x : LGroup B k) = LGroup.mk y :=
  Quotient.sound h

/-- `[C, φ] + [C', φ'] = [C ⊞ C', φ ⊕ φ']`. -/
noncomputable instance instAdd (k : ℤ) : Add (LGroup B k) where
  add := Quotient.map₂ SymPoincare.sum (fun _ _ hx _ _ hy => cobordant_sum_laws.1 _ _ _ _ hx hy)

/-- The zero `[0, 0]`. -/
noncomputable instance instZero (k : ℤ) : Zero (LGroup B k) where
  zero := LGroup.mk (SymPoincare.zero k)

/-- `-[C, φ] = [C, -φ]`. -/
instance instNeg (k : ℤ) : Neg (LGroup B k) where
  neg := Quotient.map SymPoincare.neg (fun _ _ h => cobordant_sum_laws.2.1 _ _ h)

/-- The abelian group structure on `L_k(B)`: `[C, φ] + [C', φ'] = [C ⊞ C', φ ⊕ φ']`, zero
`[0, 0]`, negation `-[C, φ] = [C, -φ]`. -/
noncomputable instance instAddCommGroup (k : ℤ) : AddCommGroup (LGroup B k) where
  add_assoc a b c := by
    induction a using Quotient.ind
    induction b using Quotient.ind
    induction c using Quotient.ind
    exact mk_eq_mk (cobordant_sum_laws.2.2.1 _ _ _)
  zero_add a := by
    induction a using Quotient.ind
    exact mk_eq_mk (cobordant_sum_laws.2.2.2.2.1 _)
  add_zero a := by
    induction a using Quotient.ind
    exact mk_eq_mk ((cobordant_equivalence B k).trans (cobordant_sum_laws.2.2.2.1 _ _)
      (cobordant_sum_laws.2.2.2.2.1 _))
  add_comm a b := by
    induction a using Quotient.ind
    induction b using Quotient.ind
    exact mk_eq_mk (cobordant_sum_laws.2.2.2.1 _ _)
  neg_add_cancel a := by
    induction a using Quotient.ind
    exact mk_eq_mk (cobordant_sum_laws.2.2.2.2.2 _)
  nsmul := nsmulRec
  zsmul := zsmulRec

lemma mk_add {k : ℤ} (x y : SymPoincare B k) :
    LGroup.mk x + LGroup.mk y = LGroup.mk (x.sum y) :=
  rfl

private lemma mk_neg {k : ℤ} (x : SymPoincare B k) : -LGroup.mk x = LGroup.mk x.neg :=
  rfl

lemma mk_zero (k : ℤ) : (0 : LGroup B k) = LGroup.mk (SymPoincare.zero k) :=
  rfl

end LGroup

end HSP
