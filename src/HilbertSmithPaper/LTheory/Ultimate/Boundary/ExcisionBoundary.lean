import HilbertSmithPaper.LTheory.Ultimate.Boundary.ExcisivePair
import HilbertSmithPaper.LTheory.Ultimate.Boundary.UltimateBoundary
import HilbertSmithPaper.LTheory.Ultimate.Groups.InducedMap

/-!
# Excision boundary

For an excisive pair `(𝒰_A, 𝒰_B)` in `𝒜`, with `r` as in its definition,
`∂_{A,B} := ∂ ∘ r_* ∘ (q_B)_* : 𝕃_k(𝒜) → 𝕃_k(𝒜/𝒰_B) → 𝕃_k(𝒰_A/𝒰_Y) → 𝕃_{k-1}(𝒰_Y)`, where `∂` is
the ultimate boundary of `𝒰_Y ⊂ 𝒰_A` and the other maps are induced maps.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

universe v u

variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A]

/-- The excision boundary `∂_{A,B} = ∂ ∘ r_* ∘ (q_B)_* : 𝕃_k(𝒜) → 𝕃_{k-1}(𝒰_Y)`. -/
noncomputable def ExcisivePair.boundary (P : ExcisivePair A) (k : ℤ) :
    ultL A k →+ ultL (ExcisivePair.inter P.UA P.UB).FullSubcategory (k - 1) :=
  (ultBoundary P.filtY k).comp ((ultL.map P.r k).comp (ultL.map (FiltQuot.q P.UB) k))

end HSP
