import Mathlib
import HilbertSmithPaper.Signatures.Real.RealMatrix
import HilbertSmithPaper.LTheory.Base.Categories.KaroubiDuality

/-!
# Real cohomology

For a chain complex `C` in `Kar Free(ℚ[G])` with `C_r = (n_r, e_r)`, the real cohomology
`H^r(C; ℝ)` (`HSP.realHco C r`) is the cohomology in degree `r` of the real cochains
`im(e_rᵀ) ⊆ ℝ^{G × Fin n_r}` with the coboundary `dᵀ`: the real cocycles `im(e_rᵀ) ∩ ker d_{r+1}ᵀ`
modulo the real coboundaries `d_rᵀ(im e_{r-1}ᵀ)`.

Lean encoding: in `Kar Free(ℚ[G])` the dual of `(n, e)` is `(n, eᵀ)` and the dual of a morphism is
its transpose, so the cochains are written with the duality: `im(e_rᵀ)` is the range of the real
idempotent of `(C_r)^*` and `d^T` is the real matrix of `d^*`.
-/

open CategoryTheory CategoryTheory.Idempotents

namespace HSP

open DualCat FreeCat

variable {G : Type} [AddGroup G] [Fintype G] [DecidableEq G]
  (C : ChainComplex (Karoubi (FreeCat G)) ℤ) (r : ℤ)

/-- The real cocycles `im(e_rᵀ) ∩ ker d_{r+1}ᵀ`. -/
private noncomputable def realCocycles : Submodule ℝ (G × Fin (C.X r).X.n → ℝ) :=
  LinearMap.range (realMap (dual (C.X r)).p) ⊓
    LinearMap.ker (realMap (dualHom (C.d (r + 1) r)).f)

/-- The real coboundaries `d_rᵀ(im e_{r-1}ᵀ)`. -/
private noncomputable def realCoboundaries : Submodule ℝ (G × Fin (C.X r).X.n → ℝ) :=
  (LinearMap.range (realMap (dual (C.X (r - 1))).p)).map (realMap (dualHom (C.d r (r - 1))).f)

/-- **Real cohomology** `H^r(C; ℝ)`: real cocycles `im(e_rᵀ) ∩ ker d_{r+1}ᵀ` modulo real
coboundaries `d_rᵀ(im e_{r-1}ᵀ)`. -/
abbrev realHco : Type :=
  realCocycles C r ⧸ (realCoboundaries C r).comap (realCocycles C r).subtype

end HSP
