import Mathlib
import HilbertSmithPaper.LTheory.Localization.Products.BoxPairingPow
import HilbertSmithPaper.LTheory.Localization.Products.SymmetricLine
import HilbertSmithPaper.LTheory.Localization.Products.Bookkeeping.ProductTotal
import HilbertSmithPaper.LTheory.Localization.Products.Bookkeeping.ProductSupport

/-!
# Bounds of products with the line

If the chain objects of a complex `C` in `Kar C_{ℤ^j} A` are zero objects outside `[0, m]`, those of
`C ⊗ Λ` are zero objects outside `[0, m + 1]`, since those of `Λ` are zero objects outside `[0, 1]`.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents

namespace HSP

universe v u

variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A]

/-- **Bounds of products with the line.** The chain objects of `C ⊗ Λ` vanish outside
`[0, m + 1]` when those of `C` vanish outside `[0, m]`. -/
theorem cxProd_line_isZero {j : ℕ} {C : ChainComplex (Karoubi (BoundedPow A j)) ℤ} {m : ℤ}
    (hC : ∀ r : ℤ, r < 0 ∨ m < r → IsZero (C.X r)) (hCf : {r | ¬ IsZero (C.X r)}.Finite)
    (hΛ : {r | ¬ IsZero (symLine.X r)}.Finite) (r : ℤ) (hr : r < 0 ∨ m + 1 < r) :
    IsZero ((cxProd (boxPairingPow A j) C symLine hCf hΛ).X r) := by
  rw [IsZero.iff_id_eq_zero, ← cxProd.total]
  refine Finset.sum_eq_zero fun x hx => ?_
  rw [cxProd.mem_supp] at hx
  obtain ⟨⟨h1, h2⟩, h3⟩ := hx
  exfalso
  have hp : 0 ≤ x.1 ∧ x.1 ≤ m := by
    by_contra h
    exact h1 (hC _ (by omega))
  have hq : x.2 = 0 ∨ x.2 = 1 := by
    by_contra h
    exact h2 (symLine.isZero_X h)
  omega

end HSP
