import Mathlib
import HilbertSmithPaper.LTheory.Base.Pairs.PoincarePair
import HilbertSmithPaper.LTheory.Bounded.Categories.IteratedBoundedCategory
import HilbertSmithPaper.LTheory.Localization.Products.BoxPairingPow
import HilbertSmithPaper.LTheory.Localization.Products.ExternalProduct
import HilbertSmithPaper.LTheory.Localization.Products.SymmetricLineStructure

/-!
# Product of a pair with the line

For a strict `k`-dimensional symmetric Poincaré pair `(f : C ⟶ D, δφ, φ)` in `Kar C_{ℤ^j} A`,
`(f ⊗ 1 : C ⊗ Λ ⟶ D ⊗ Λ, δφ ⊗ λ, φ ⊗ λ)` is a strict `(k+1)`-dimensional symmetric Poincaré
pair in `Kar C_{ℤ^{j+1}} A`, with boundary `(C ⊗ Λ, φ ⊗ λ)` (no sign). The products are taken
for the box product pairing `Kar C_{ℤ^j} A × C_ℤ(ℚ) → Kar C_{ℤ^{j+1}} A`.

Lean: the finiteness of the nonzero chain objects, needed to form the products, is a hypothesis
(any proof will do).
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents

namespace HSP

universe v u

variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A]

/-- **Product of a pair with the line.** `(f ⊗ 1, δφ ⊗ λ, φ ⊗ λ)` is a strict
`(n+1)`-dimensional symmetric Poincaré pair with boundary `(C ⊗ Λ, φ ⊗ λ)`. -/
theorem SymPair.exists_prod_line {j : ℕ} {m n : ℤ} (W : SymPair (Karoubi (BoundedPow A j)) m n)
    (hC : {r | ¬ IsZero (W.C.X r)}.Finite) (hD : {r | ¬ IsZero (W.D.X r)}.Finite)
    (hΛ : {r | ¬ IsZero (symLine.X r)}.Finite) :
    ∃ W' : SymPair (Karoubi (BoundedPow A (j + 1))) (m + 1) (n + 1),
      W'.data = ⟨cxProd (boxPairingPow A j) W.C symLine hC hΛ,
        cxProd (boxPairingPow A j) W.D symLine hD hΛ,
        cxProdMap (boxPairingPow A j) W.f (𝟙 symLine) hC hΛ hD hΛ,
        strProd (boxPairingPow A j) hD hΛ W.δφ symLine.str (n + 1) rfl,
        strProd (boxPairingPow A j) hC hΛ W.φ symLine.str (m + 1) rfl⟩ := by
  sorry

end HSP
