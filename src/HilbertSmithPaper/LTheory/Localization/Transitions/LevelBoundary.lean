import Mathlib
import HilbertSmithPaper.LTheory.Localization.Boundary.LocalizationBoundary
import HilbertSmithPaper.LTheory.Localization.Transitions.DecoratedTransition
import HilbertSmithPaper.LTheory.Localization.Transitions.LowerLGroup

/-!
# Stage boundary

For an involution-invariant Karoubi filtration `𝒰 ⊂ 𝒜` and `j ≥ 0`, the stage boundary is
`∂^{(j)} = ∂ ∘ t^{im} : L^{⟨-j⟩}_k(𝒜/𝒰) → L^p_{k+j}(C_{ℤ^{j+1}}𝒰)`, with `t^{im}` the decorated
transition at stage `j` and `∂` the localization boundary of the filtration
`C_{ℤ^{j+1}}𝒰 ⊂ C_{ℤ^{j+1}}𝒜`.

Lean: `C_{ℤ^{j+1}}𝒰` is the full subcategory `Bounded.subPow U (j + 1)` of `C_{ℤ^{j+1}}𝒜`, and
the target degree is written `k + j + 1 - 1`, the degree of the localization boundary on
`L^{im}_{k+j+1}`.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents

namespace HSP

universe v u

variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A] {U : ObjectProperty A} [IsDualAdditive U]

/-- **Stage boundary.** `∂^{(j)} = ∂ ∘ t^{im} : L^{⟨-j⟩}_k(𝒜/𝒰) → L^p_{k+j}(C_{ℤ^{j+1}}𝒰)`. -/
noncomputable def levelBoundary (F : KaroubiFiltration U) (j : ℕ) (k : ℤ) :
    lowerL (FiltQuot U) j k →+ Lp (Bounded.subPow U (j + 1)).FullSubcategory (k + j + 1 - 1) :=
  (locBoundary (Bounded.powKaroubiFiltration F (j + 1)) (k + j + 1)).comp
    (decTransition F j (m := k + j) rfl)

end HSP
