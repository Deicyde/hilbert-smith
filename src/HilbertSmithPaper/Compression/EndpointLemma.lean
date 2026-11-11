import Mathlib
import HilbertSmithPaper.Compression.CompressionProductRule
import HilbertSmithPaper.Compression.BoundSequence
import HilbertSmithPaper.Corner.Actions.ExteriorWitness
import HilbertSmithPaper.Corner.Exterior

/-!
# Endpoint lemma

Let `i ≥ i₀`, `M_0, M_1, M_2 ∈ {D_i, D_i^{N-*}}` with retained projections `p_j`, inclusions `ȷ_j`
and `Q_1 = 1 - ȷ_1 p_1`, and `α : M_1 → M_2`, `β : M_0 → M_1` in `𝒫_i` with types `c_α, c_β`. Let
`W` be the span in `M_1` of the discarded cells that lie in `𝓑_i(u)`, with the control labels, and
`ι_W`, `p_W` its inclusion and projection. Then `p_2 α Q_1 β ȷ_0 = x y` with `y = p_W β ȷ_0` and
`x = p_2 α ι_W`; `y` has graph type `c_β` and `x` graph type `c_α`, both with bound `δ_i`; every
label of `W` lies in `Z = T × Z_0`. Hence `p_2 α Q_1 β ȷ_0` is an exterior witness of type
`c_α + c_β` with bound `δ_i`.

## Encoding

* As in `compress`, the cells of `M_j` are the cells of `D_i` in a degree `r_j` (for a dual cell,
  the degree of the underlying cell), with labels `chainModelLabel _ i r_j`; then `p_j = pr`,
  `ȷ_j = in` and `Q_1 = Q` in these degrees. Membership in `𝒫_i` is
  `TypedMatrix.mk _ _ (labels) (labels) α c_α ∈ chainModelFamily _ _ _ i` (the constructor of
  typed matrices).
* `W` is the type of buffered cells `b ∈ 𝓑_i(u)` of degree `r_1` (for the pinch radius of the
  fixed local data) that are not retained; `μ` gives each its control label
  `controlLabel _ _ _ _ u b`; `ι_W` is the based inclusion matrix and `p_W = ι_Wᵀ`.
* The compressed cells carry the labels `(compressed F r).as.x i` of the compressed complex; the
  bound is the bound sequence `bound F i`; `Z = T × Z_0` is `Set.univ ×ˢ exterior n R`.
* Membership in `W` and the matrix products over `W` use classical decidability.
* `endpoint` (the declaration of the article) is the conjunction of (1)-(3) and the witness.
-/

namespace HSP.Compression

open HSP.ChainModels HSP.Corner FreeQ
open scoped Matrix

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

open Classical in
/-- **Endpoint lemma.** For `i ≥ i₀` and `α, β ∈ 𝒫_i` of types `c_α, c_β`,
`p_2 α Q_1 β ȷ_0 = x y` through the discarded buffered cells `W`, with `y = p_W β ȷ_0` of graph
type `c_β` and `x = p_2 α ι_W` of graph type `c_α`, both with bound `δ_i`, and every label of `W`
in `T × Z_0`; hence `p_2 α Q_1 β ȷ_0` is an exterior witness of type `c_α + c_β` with bound
`δ_i`. -/
theorem endpoint (F : FixedLocalData p n D ρplus) {i : ℕ} (hi : startIndex F ≤ i)
    {r₀ r₁ r₂ : ℤ}
    (α : Matrix (Fin ((chainModel F.toLocalDatum i).X r₂).dim)
      (Fin ((chainModel F.toLocalDatum i).X r₁).dim) ℚ)
    (β : Matrix (Fin ((chainModel F.toLocalDatum i).X r₁).dim)
      (Fin ((chainModel F.toLocalDatum i).X r₀).dim) ℚ) {cα cβ : ZMod p}
    (hα : TypedMatrix.mk _ _ (chainModelLabel F.toLocalDatum i r₁)
      (chainModelLabel F.toLocalDatum i r₂) α cα ∈
        chainModelFamily F.toLocalDatum F.ρ_pos F.ρ_lt i)
    (hβ : TypedMatrix.mk _ _ (chainModelLabel F.toLocalDatum i r₀)
      (chainModelLabel F.toLocalDatum i r₁) β cβ ∈
        chainModelFamily F.toLocalDatum F.ρ_pos F.ρ_lt i) :
    let W : Type :=
      {b : bufferedCells F.toLocalDatum F.ρ (chainModelLabel F.toLocalDatum i r₁) F.u //
        ¬ IsRetained F i r₁ b.1}
    let μ : W → F.T × RoundSphere n := fun w =>
      controlLabel F.toLocalDatum F.ρ_pos F.ρ_lt (chainModelLabel F.toLocalDatum i r₁) F.u w.1
    let ιW : Matrix (Fin ((chainModel F.toLocalDatum i).X r₁).dim) W ℚ :=
      Matrix.of fun a w => if a = w.1.1 then 1 else 0
    let y := ιWᵀ * β * retainedInc F i r₀
    let x := retainedProj F i r₂ * α * ιW
    let Z : Set (F.T × RoundSphere n) := (Set.univ : Set F.T) ×ˢ exterior n F.R
    -- (1)
    retainedProj F i r₂ * α * discardProj F i r₁ * β * retainedInc F i r₀ = x * y ∧
    -- (2)
    IsGraphType ((compressed F r₀).as.x i) μ cβ (bound F i) y ∧
      IsGraphType μ ((compressed F r₂).as.x i) cα (bound F i) x ∧
    -- (3)
    (∀ w, μ w ∈ Z) ∧
    IsExteriorWitness Z ((compressed F r₀).as.x i) ((compressed F r₂).as.x i) (cα + cβ)
      (bound F i) (retainedProj F i r₂ * α * discardProj F i r₁ * β * retainedInc F i r₀) := by
  sorry

end HSP.Compression
