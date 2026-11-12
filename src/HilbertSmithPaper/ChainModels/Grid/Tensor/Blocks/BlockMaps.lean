import Mathlib
import HilbertSmithPaper.LTheory.Localization.Products.Bookkeeping.BasedCategory

/-!
# Block inclusions and projections

For `d : Fin m → ℕ`, `blockInc d j` and `blockProj d j` are the inclusion and projection of the
`j`-th block `ℚ^{d_j}` of `ℚ^{∑ d}`, the blocks enumerated by `finSigmaFinEquiv` (concatenation
in increasing `j`).
-/

open CategoryTheory

namespace HSP.ChainModels

open FreeQ

/-- The inclusion of the `j`-th block `ℚ^{d_j}` into `ℚ^{∑ d}`. -/
def blockInc {m : ℕ} (d : Fin m → ℕ) (j : Fin m) : (⟨d j⟩ : FreeQ) ⟶ ⟨∑ i, d i⟩ :=
  ofMatrix (Matrix.of fun a b => if finSigmaFinEquiv.symm a = ⟨j, b⟩ then 1 else 0)

/-- The projection of `ℚ^{∑ d}` onto its `j`-th block `ℚ^{d_j}`. -/
def blockProj {m : ℕ} (d : Fin m → ℕ) (j : Fin m) : (⟨∑ i, d i⟩ : FreeQ) ⟶ ⟨d j⟩ :=
  ofMatrix (Matrix.of fun b a => if finSigmaFinEquiv.symm a = ⟨j, b⟩ then 1 else 0)

end HSP.ChainModels
