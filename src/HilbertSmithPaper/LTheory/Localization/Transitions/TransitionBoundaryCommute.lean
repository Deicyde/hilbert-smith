import HilbertSmithPaper.LTheory.Localization.Transitions.LevelBoundary
import HilbertSmithPaper.LTheory.Localization.Transitions.TransitionMap
import HilbertSmithPaper.LTheory.Ultimate.Boundary.SubPowIdent
import HilbertSmithPaper.LTheory.Ultimate.Groups.UltimateCls
import HilbertSmithPaper.LTheory.Base.Groups.InducedMap

/-!
# Transition commutes with the boundary

For an involution-invariant Karoubi filtration `𝒰 ⊂ 𝒜`, `j ≥ 0` and
`x ∈ L^{⟨-j⟩}_k(𝒜/𝒰)`, `t (∂^{(j)} x) = ∂^{(j+1)} (t x)` in `L^{⟨-j-2⟩}_{k-1}(𝒰)`, where on the left
`t` is the transition map of `𝒰` at stage `j + 1` and on the right that of `𝒜/𝒰` at stage `j`.

Lean: the stage boundary `levelBoundary F j k` lands in `L^p_{k+j+1-1}` of the full subcategory
`C_{ℤ^{j+1}}𝒰 ⊂ C_{ℤ^{j+1}}𝒜`. It is read in `L^{⟨-j-1⟩}_{k-1}(𝒰)` through the identification
`Bounded.subPowIdent` of that full subcategory with `C_{ℤ^{j+1}}(𝒰)`, followed by the transport
along `k + j + 1 - 1 = (k - 1) + (j + 1)`.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents

namespace HSP

universe v u

variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A] {U : ObjectProperty A} [IsDualAdditive U]

/-- `t (∂^{(j)} x) = ∂^{(j+1)} (t x)`, with `∂^{(j)}` read in `L^{⟨-j-1⟩}_{k-1}(𝒰)`. -/
theorem transitionLower_levelBoundary (F : KaroubiFiltration U) (j : ℕ) (k : ℤ)
    (x : lowerL (FiltQuot U) j k) :
    transitionLower U.FullSubcategory (j + 1) (k - 1)
        (LGroup.castIndex (B := Karoubi (BoundedPow U.FullSubcategory (j + 1)))
          (show k + j + 1 - 1 = k - 1 + ((j + 1 : ℕ) : ℤ) by push_cast; ring)
          (Lp.map (Bounded.subPowIdent U (j + 1)) (k + j + 1 - 1) (levelBoundary F j k x))) =
      LGroup.castIndex (B := Karoubi (BoundedPow U.FullSubcategory (j + 1 + 1)))
          (show k + ((j + 1 : ℕ) : ℤ) + 1 - 1 = k - 1 + ((j + 1 + 1 : ℕ) : ℤ) by push_cast; ring)
          (Lp.map (Bounded.subPowIdent U (j + 1 + 1)) (k + ((j + 1 : ℕ) : ℤ) + 1 - 1)
            (levelBoundary F (j + 1) k (transitionLower (FiltQuot U) j k x))) := by
  sorry

end HSP
