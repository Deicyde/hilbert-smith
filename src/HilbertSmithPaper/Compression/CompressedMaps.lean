import Mathlib
import HilbertSmithPaper.ChainModels.Approximations.AdjointHomotopy
import HilbertSmithPaper.ChainModels.Approximations.ChosenProductHomotopies
import HilbertSmithPaper.Compression.CompressedComplex
import HilbertSmithPaper.Compression.RetainedProjection
import HilbertSmithPaper.ChainModels.Approximations.AdjointHomotopies

/-!
# Compressed maps

For `M_1, M_2 ∈ {D_i, D_i^{N-*}}`, with `p_2` the retained projection of `M_2` and `ȷ_1` the
retained inclusion of `M_1` (`pr_i`, `in_i` on chains, `in_i^*`, `pr_i^*` on cochains), the
compression of `w : M_1 → M_2` is `ŵ = p_2 w ȷ_1` for `i ≥ i₀` and `0` for `i < i₀`. The compressed
maps are the compressions of `d` (on `D_i` and on `D_i^{N-*}`), `φ_i`, `b_i`, `H_i`, `H'_i`, `a_g`,
`B_{g,h}`, `V_g`.

## Encoding

* A cell of `(D_i^{N-*})_r = ((D_i)_{N-r})^*` is a cell of `(D_i)_{N-r}`, and `in_i^*`, `pr_i^*`
  are the transposes of `in_i`, `pr_i`; so in every case `p_2 = pr_i` and `ȷ_1 = in_i` in the
  degrees of the underlying cells. `compress F i r s w` (the declaration of the article) is
  `pr_i w in_i` for a matrix `w` from the cells of `(D_i)_r` to those of `(D_i)_s`; for `i < i₀`
  the ranks are `0`, so `ŵ = 0`.
* The named compressed maps are abbreviations, in each degree (each component for the elements
  `φ_i`, `V_g` of the structure complex), `N = n + 4`, with `B_{g,h}`, `V_g` the chosen ones for
  the pinch radius of the fixed local data.
-/

open CategoryTheory

namespace HSP.Compression

open HSP.ChainModels FreeQ DualCat

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- The *compression* `ŵ = pr_i w in_i` of a matrix `w` from the cells of `(D_i)_r` to those of
`(D_i)_s` (zero for `i < i₀`, where the compressed ranks vanish). -/
noncomputable def compress (F : FixedLocalData p n D ρplus) (i : ℕ) (r s : ℤ)
    (w : Matrix (Fin ((chainModel F.toLocalDatum i).X s).dim)
      (Fin ((chainModel F.toLocalDatum i).X r).dim) ℚ) :
    Matrix (Fin ((compressed F s).as.n i)) (Fin ((compressed F r).as.n i)) ℚ :=
  retainedProj F i s * w * retainedInc F i r

/-- `d̂` on `C`, in degree `r`. -/
noncomputable abbrev dHat (F : FixedLocalData p n D ρplus) (i : ℕ) (r : ℤ) :=
  compress F i r (r - 1) (toMatrix ((chainModel F.toLocalDatum i).d r (r - 1)))

/-- `d̂` on `C^{N-*}`, in degree `r`. -/
noncomputable abbrev dHatDual (F : FixedLocalData p n D ρplus) (i : ℕ) (r : ℤ) :=
  compress F i ((n + 4 : ℕ) - r) ((n + 4 : ℕ) - (r - 1))
    (toMatrix ((dualCx (chainModel F.toLocalDatum i) ((n + 4 : ℕ) : ℤ)).d r (r - 1)))

/-- `φ̂`, the component at `(p, q)`, `p + q = N`. -/
noncomputable abbrev phiHat (F : FixedLocalData p n D ρplus) (i : ℕ)
    (x : {x : ℤ × ℤ // x.1 + x.2 = ((n + 4 : ℕ) : ℤ)}) :=
  compress F i x.1.2 x.1.1 (toMatrix ((chainModelDuality F.toLocalDatum i).φ x))

/-- `b̂`, in degree `r`. -/
noncomputable abbrev bHat (F : FixedLocalData p n D ρplus) (i : ℕ) (r : ℤ) :=
  compress F i r ((n + 4 : ℕ) - r) (toMatrix ((chainModelDuality F.toLocalDatum i).b r))

/-- `Ĥ`, in degree `r`. -/
noncomputable abbrev HHat (F : FixedLocalData p n D ρplus) (i : ℕ) (r : ℤ) :=
  compress F i r (r + 1) (toMatrix (chainModelH F.toLocalDatum i r))

/-- `Ĥ'`, in degree `r`. -/
noncomputable abbrev H'Hat (F : FixedLocalData p n D ρplus) (i : ℕ) (r : ℤ) :=
  compress F i ((n + 4 : ℕ) - r) ((n + 4 : ℕ) - (r + 1))
    (toMatrix (chainModelH' F.toLocalDatum i r))

/-- `Â_g`, in degree `r`. -/
noncomputable abbrev AHat (F : FixedLocalData p n D ρplus) (i : ℕ) (g : ZMod (p ^ i)) (r : ℤ) :=
  compress F i r r (toMatrix (groupApprox F.toLocalDatum i g r))

/-- `B̂_{g,h}`, in degree `r`. -/
noncomputable abbrev BHat (F : FixedLocalData p n D ρplus) (i : ℕ) (g h : ZMod (p ^ i))
    (r : ℤ) :=
  compress F i r (r + 1) (toMatrix (productHomotopy F.toLocalDatum F.ρ_pos F.ρ_lt i g h r))

/-- `V̂_g`, the component at `(p, q)`, `p + q = N + 1`. -/
noncomputable abbrev VHat (F : FixedLocalData p n D ρplus) (i : ℕ) (g : ZMod (p ^ i))
    (x : {x : ℤ × ℤ // x.1 + x.2 = ((n + 4 : ℕ) : ℤ) + 1}) :=
  compress F i x.1.2 x.1.1 (toMatrix (adjointHomotopy F.toLocalDatum F.ρ_pos F.ρ_lt i g x))

end HSP.Compression
