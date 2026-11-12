import Mathlib
import HilbertSmithPaper.Signatures.Real.RealMatrix

/-!
# Real homology

For a chain complex `C` in `Kar Free(ℚ[G])` with `C_r = (n_r, e_r)`, the real chains are
`C_r(ℝ) = im(e_r) ⊆ ℝ^{G × Fin n_r}` with the real matrices of the differentials, and
`H_r(C; ℝ)` (`HSP.realH C r`) is the homology of this real complex in degree `r`: the real cycles
`im(e_r) ∩ ker d_r` modulo the real boundaries `d_{r+1}(im e_{r+1})`.

Lean encoding: the matrices are base-changed to `ℝ` entrywise (`HSP.FreeCat.realMap`) and the real
chains are the range of the real idempotent, so no tensor products are needed. Homology is the
quotient of the cycle submodule by the boundaries pulled back to it.
-/

open CategoryTheory CategoryTheory.Idempotents

namespace HSP

open FreeCat

variable {G : Type} [AddGroup G] [Fintype G] [DecidableEq G]
  (C : ChainComplex (Karoubi (FreeCat G)) ℤ) (r : ℤ)

/-- The real cycles `im(e_r) ∩ ker d_r`. -/
private noncomputable def realCycles : Submodule ℝ (G × Fin (C.X r).X.n → ℝ) :=
  LinearMap.range (realMap (C.X r).p) ⊓ LinearMap.ker (realMap (C.d r (r - 1)).f)

/-- The real boundaries `d_{r+1}(im e_{r+1})`. -/
private noncomputable def realBoundaries : Submodule ℝ (G × Fin (C.X r).X.n → ℝ) :=
  (LinearMap.range (realMap (C.X (r + 1)).p)).map (realMap (C.d (r + 1) r).f)

/-- **Real homology** `H_r(C; ℝ)`: real cycles `im(e_r) ∩ ker d_r` modulo real boundaries
`d_{r+1}(im e_{r+1})`. -/
abbrev realH : Type :=
  realCycles C r ⧸ (realBoundaries C r).comap (realCycles C r).subtype

end HSP
