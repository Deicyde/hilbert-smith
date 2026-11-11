import Mathlib
import HilbertSmithPaper.ChainModels.Grid.BoxHull
import HilbertSmithPaper.ChainModels.Grid.MeshSequence
import HilbertSmithPaper.ChainModels.Grid.Cubical.GridCell
import HilbertSmithPaper.ChainModels.Grid.Cubical.CubicalTorusGrid
import HilbertSmithPaper.ChainModels.Grid.Cubical.GridCube

/-!
# Approximation boxes

For `k ≥ k₀`, a map `L : 𝕋ⁿ → 𝕋ⁿ` and a cube `c` of `C(k)`, `Γ_L(c) = Box_k(N_h(L|c|))`, with
`h = 4/k` and `N_h` the closed `d_∞`-neighbourhood.

## Encoding

`chainApproxBox A hk L r e` (the declaration of the article) is `Γ_L(c)` for the cube `c` of the
basis vector `e` of `C(k)_r` (`gridCell k n r e`); `N_h` is `Metric.cthickening (4/k)`, and the
box hull needs `k ≥ 8`, which follows from `k ≥ k₀`.
-/

namespace HSP.ChainModels

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- `k ≥ k₀` gives `k ≥ 8`. -/
private lemma eight_le_of_meshStart_le (A : LocalDatum p n D ρplus) {k : ℕ} (hk : meshStart A ≤ k) :
    8 ≤ k :=
  (meshStart_spec A).1.trans hk

/-- `Γ_L(c) = Box_k(N_h(L|c|))`, `h = 4/k`, for the cube `c` of the basis vector `e` of
`C(k)_r`. -/
noncomputable def chainApproxBox (A : LocalDatum p n D ρplus) {k : ℕ} (hk : meshStart A ≤ k)
    (L : Torus n → Torus n) (r : ℤ) (e : Fin ((gridComplex k n).X r).dim) : GridBox k n :=
  boxHull k (eight_le_of_meshStart_le A hk)
    (Metric.cthickening (4 / k : ℝ) (L '' (gridCell k n r e).realization))

end HSP.ChainModels
