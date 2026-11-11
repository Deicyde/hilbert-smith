import Mathlib
import HilbertSmithPaper.LTheory.Bounded.Categories.IteratedBoundedQuotient
import HilbertSmithPaper.LTheory.Localization.Decorations.DecoratedObject
import HilbertSmithPaper.LTheory.Localization.Products.BoxPairingPow
import HilbertSmithPaper.LTheory.Localization.Products.ComplexProduct
import HilbertSmithPaper.LTheory.Localization.Products.SymmetricLine
import HilbertSmithPaper.LTheory.Bounded.Categories.IteratedBoundedSub
import HilbertSmithPaper.LTheory.Bounded.Categories.IteratedBoundedSubAdditive

/-!
# Products with the line are decorated

For an involution-invariant Karoubi filtration `𝒰 ⊂ 𝒜`, `j ≥ 0` and a complex `C` in
`Kar C_{ℤ^j}(𝒜/𝒰)` with finitely many nonzero chain objects, every chain object `X` of `C ⊗ Λ`
has `[X] = 0` in `K_0(Kar C_{ℤ^{j+1}}(𝒜/𝒰))`, so `(Kar e_{j+1}^{-1})(X)` is decorated for the
filtration `C_{ℤ^{j+1}}𝒰 ⊂ C_{ℤ^{j+1}}𝒜`.

Lean: the finiteness of the nonzero chain objects of `C` and of `Λ` are hypotheses (any proofs
will do); `e_{j+1}^{-1}` is the second component of `Bounded.powQuotientIso F (j + 1)`.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents

namespace HSP

universe v u

variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A] {U : ObjectProperty A} [IsDualAdditive U]

/-- **Products with the line are decorated.** Every chain object `X` of `C ⊗ Λ` has `[X] = 0`,
and `(Kar e_{j+1}^{-1})(X)` is decorated. -/
theorem cxProd_line_decorated (F : KaroubiFiltration U) (j : ℕ)
    (C : ChainComplex (Karoubi (BoundedPow (FiltQuot U) j)) ℤ)
    (hC : {r | ¬ IsZero (C.X r)}.Finite) (hΛ : {r | ¬ IsZero (symLine.X r)}.Finite) (r : ℤ) :
    K0.cls ((cxProd (boxPairingPow (FiltQuot U) j) C symLine hC hΛ).X r) = 0 ∧
      IsDecorated (Bounded.subPow U (j + 1))
        ((Bounded.powQuotientIso F (j + 1)).1.2.kar.toFunctor.obj
          ((cxProd (boxPairingPow (FiltQuot U) j) C symLine hC hΛ).X r)) := by
  sorry

end HSP
