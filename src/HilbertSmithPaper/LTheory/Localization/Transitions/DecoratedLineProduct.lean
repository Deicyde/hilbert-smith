import Mathlib
import HilbertSmithPaper.LTheory.Localization.Decorations.ComplexInSubcategory
import HilbertSmithPaper.LTheory.Localization.Transitions.LineProductDecorated
import HilbertSmithPaper.LTheory.Localization.Transitions.TransitionComplex
import HilbertSmithPaper.LTheory.Bounded.Categories.IteratedBoundedSub
import HilbertSmithPaper.LTheory.Bounded.Categories.IteratedBoundedSubAdditive
import HilbertSmithPaper.LTheory.Base.Complexes.FiniteBounded

/-!
# Decorated product with the line

For an involution-invariant Karoubi filtration `𝒰 ⊂ 𝒜`, `j ≥ 0` and a strict `m`-dimensional
symmetric Poincaré complex `(C, φ)` in `Kar C_{ℤ^j}(𝒜/𝒰)`, the complex
`(e_{j+1}^{-1}(C ⊗ Λ), (e_{j+1}^{-1})_%(φ ⊗ λ))` is a strict `m'`-dimensional symmetric Poincaré
complex (`m' = m + 1`) in `Dec(C_{ℤ^{j+1}}𝒜/C_{ℤ^{j+1}}𝒰)`: its chain objects are decorated.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents

namespace HSP

universe v u

variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A] {U : ObjectProperty A} [IsDualAdditive U]

/-- **Decorated product with the line.** `(e_{j+1}^{-1}(C ⊗ Λ), (e_{j+1}^{-1})_%(φ ⊗ λ))` as a
strict `m'`-dimensional symmetric Poincaré complex in `Dec(C_{ℤ^{j+1}}𝒜/C_{ℤ^{j+1}}𝒰)`. -/
noncomputable def decTransitionCx (F : KaroubiFiltration U) (j : ℕ) {m m' : ℤ} (hm : m + 1 = m')
    (x : SymPoincare (Karoubi (BoundedPow (FiltQuot U) j)) m) :
    SymPoincare (Dec (Bounded.subPow U (j + 1))) m' :=
  SymPoincare.toSub (IsDecorated (Bounded.subPow U (j + 1)))
    (SymPoincare.map (Bounded.powQuotientIso F (j + 1)).1.2.kar (transitionCx hm x))
    fun r => (cxProd_line_decorated F j x.C (finite_of_bounded x.bounded)
      (finite_of_bounded (k := 1) fun _ h => symLine.isZero_X (by omega)) r).2

end HSP
