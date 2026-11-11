import Mathlib
import HilbertSmithPaper.Compression.CompressedMaps

/-!
# Product rule

For `M_0, M_1, M_2 ∈ {D_i, D_i^{N-*}}` with retained projections `p_j`, inclusions `ȷ_j` and
`Q_1 = 1 - ȷ_1 p_1`, and matrices `α : M_1 → M_2`, `β : M_0 → M_1`,
`α̂ β̂ - (αβ)^ = -p_2 α Q_1 β ȷ_0`.

## Encoding

* As in `compress`, a cell of `D_i^{N-*}` is a cell of `D_i` in the complementary degree, and on
  cochains `in_i^*`, `pr_i^*`, `Q_i^*` are the transposes of `in_i`, `pr_i`, `Q_i`, so in every
  case `p_j = pr_i`, `ȷ_j = in_i` and `Q_1 = Q_i` (`discardProj`) in the degrees `r_0, r_1, r_2`
  of the underlying cells. One statement over these degrees covers all eight cases.
* The article states the rule for `i ≥ i₀`; it holds for every `i` (for `i < i₀` all compressed
  ranks are `0`), so `product_rule` (the declaration of the article) has no hypothesis on `i`.
-/

namespace HSP.Compression

open HSP.ChainModels

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- **Product rule.** `α̂ β̂ - (αβ)^ = -p_2 α Q_1 β ȷ_0` for matrices `α` from the cells of
degree `r₁` to those of degree `r₂` and `β` from degree `r₀` to degree `r₁`. -/
theorem product_rule (F : FixedLocalData p n D ρplus) (i : ℕ) (r₀ r₁ r₂ : ℤ)
    (α : Matrix (Fin ((chainModel F.toLocalDatum i).X r₂).dim)
      (Fin ((chainModel F.toLocalDatum i).X r₁).dim) ℚ)
    (β : Matrix (Fin ((chainModel F.toLocalDatum i).X r₁).dim)
      (Fin ((chainModel F.toLocalDatum i).X r₀).dim) ℚ) :
    compress F i r₁ r₂ α * compress F i r₀ r₁ β - compress F i r₀ r₂ (α * β) =
      -(retainedProj F i r₂ * α * discardProj F i r₁ * β * retainedInc F i r₀) := by
  simp only [compress, discardProj, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
    Matrix.mul_assoc]
  abel

end HSP.Compression
