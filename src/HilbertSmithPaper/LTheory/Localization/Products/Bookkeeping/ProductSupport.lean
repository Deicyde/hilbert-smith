import Mathlib

/-!
# Support of a tensor product of complexes

For complexes `C` and `D` (indexed by `ℤ`) with finitely many chain objects that are not zero
objects, and `r ∈ ℤ`, the support in degree `r` is the finite set of pairs `(p, q)` with
`p + q = r` such that neither `C_p` nor `D_q` is a zero object.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

universe v₁ v₂ u₁ u₂

namespace cxProd

variable {B : Type u₁} [Category.{v₁} B] [Preadditive B]
  {E : Type u₂} [Category.{v₂} E] [Preadditive E]
  {C : ChainComplex B ℤ} {D : ChainComplex E ℤ}
  (hC : {r | ¬ IsZero (C.X r)}.Finite) (hD : {r | ¬ IsZero (D.X r)}.Finite)

/-- **Support of a tensor product.** The pairs `(p, q)` with `p + q = r` where both `C_p` and
`D_q` are nonzero. -/
noncomputable def supp (r : ℤ) : Finset (ℤ × ℤ) :=
  (hC.toFinset ×ˢ hD.toFinset).filter fun x => x.1 + x.2 = r

lemma mem_supp {r : ℤ} {x : ℤ × ℤ} :
    x ∈ supp hC hD r ↔ (¬ IsZero (C.X x.1) ∧ ¬ IsZero (D.X x.2)) ∧ x.1 + x.2 = r := by
  simp [supp]

end cxProd

end HSP
