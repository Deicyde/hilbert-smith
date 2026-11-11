import HilbertSmithPaper.LTheory.Ultimate.Groups.LowerLSequence

/-!
# Ultimate L-group

`𝕃_k(A)` is the colimit of the sequence of groups
`L^{⟨0⟩}_k(A) → L^{⟨-1⟩}_k(A) → L^{⟨-2⟩}_k(A) → ⋯` along the transition maps `t`.

Lean: the colimit is taken in `AddCommGrpCat`.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

universe v u

variable (A : Type u) [Category.{v} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A]

/-- The ultimate L-group `𝕃_k(A)`, the colimit of the lower L-groups `L^{⟨-j⟩}_k(A)` along the
transition maps. -/
noncomputable def ultL (k : ℤ) : Type (max u v) :=
  AddCommGrpCat.carrier (colimit (lowerLSeq A k))

noncomputable instance (k : ℤ) : AddCommGroup (ultL A k) :=
  (colimit (lowerLSeq A k)).str

end HSP
