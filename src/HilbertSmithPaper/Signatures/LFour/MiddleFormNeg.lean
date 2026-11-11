import Mathlib
import HilbertSmithPaper.Signatures.LFour.MiddleForm
import HilbertSmithPaper.LTheory.Base.Pairs.SumOfPoincare

/-!
# Middle form of the negative

`b_{(C, -φ)} = -b_{(C, φ)}` on the same space `H^2(C; ℝ)` (`HSP.middleForm_neg`): the real
cohomology does not involve `φ`, and `b` is linear in `φ_2`.
-/

open CategoryTheory CategoryTheory.Idempotents

namespace HSP

open FreeCat

variable {G : Type} [AddGroup G] [Fintype G] [DecidableEq G]

/-- The middle form of `(C, -φ)` is `-b_{(C, φ)}`. -/
theorem middleForm_neg (x : SymPoincare (Karoubi (FreeCat G)) 4) :
    middleForm (SymPoincare.neg x) = -middleForm x := by
  refine LinearMap.ext fun a => LinearMap.ext fun b => ?_
  induction a using Submodule.Quotient.induction_on with | H a => ?_
  induction b using Submodule.Quotient.induction_on with | H b => ?_
  have hneg : ((SymPoincare.neg x).φ ⟨(2, 2), by norm_num⟩).f =
      -(x.φ ⟨(2, 2), by norm_num⟩).f := rfl
  change a.1 ⬝ᵥ realMap ((SymPoincare.neg x).φ ⟨(2, 2), _⟩).f b.1 =
    -(a.1 ⬝ᵥ realMap (x.φ ⟨(2, 2), by norm_num⟩).f b.1)
  rw [hneg]
  erw [realMap_neg]
  rw [LinearMap.neg_apply, dotProduct_neg]
  rfl

end HSP
