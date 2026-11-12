import Mathlib
import HilbertSmithPaper.ChainModels.Grid.Cubical.GridCell
import HilbertSmithPaper.ChainModels.Grid.Cubical.CubicalTorusGrid
import HilbertSmithPaper.ChainModels.Grid.Cubical.GridCube

/-!
# The span of a set of cubes

Chains of `C(k)_r` are columns `Fin dim → ℚ`. `cubeSpan S r` is the span in `C(k)_r` of the
basis cubes in `S`: the columns vanishing off `S`.
-/

namespace HSP.ChainModels

open FreeQ Matrix

/-- The span in `C(k)_r` of the basis cubes in `S`: the columns vanishing off `S`. -/
def cubeSpan {k n : ℕ} (S : Set (GridCube k n)) (r : ℤ) :
    Submodule ℚ (Fin ((gridComplex k n).X r).dim → ℚ) where
  carrier := {z | ∀ a, gridCell k n r a ∉ S → z a = 0}
  add_mem' {x y} hx hy a ha := by simp [hx a ha, hy a ha]
  zero_mem' _ _ := rfl
  smul_mem' c x hx a ha := by simp [hx a ha]

end HSP.ChainModels
