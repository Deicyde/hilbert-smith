import Mathlib
import HilbertSmithPaper.ChainModels.Grid.Cubical.CubicalTorusGrid
import HilbertSmithPaper.ChainModels.Grid.Cubical.UnitComplex
import HilbertSmithPaper.ChainModels.Grid.Cubical.CircleDimNeg
import HilbertSmithPaper.ChainModels.Grid.Cubical.CircleComplex
import HilbertSmithPaper.ChainModels.Grid.Poincare.CircleData.CircleB
import HilbertSmithPaper.ChainModels.Grid.Tensor.StructureProducts.BasedDualProd

/-!
# The iterated grid duality map

`b^{(n)} = (⋯(1 ⊗ b) ⊗ ⋯) ⊗ b : C(k) → C(k)^{n-*}` through `Ξ^{-1}`, by components.
-/

open CategoryTheory

namespace HSP.ChainModels

open FreeQ DualCat

/-- *The iterated grid duality map* `b^{(n)} : C(k) → C(k)^{n-*}`, by components: `b^{(0)}` is the
identity of `ℚ` in degree `0` on the unit complex, and `b^{(n+1)}` is the product of duality maps
of `b^{(n)}` and the circle inverse `b` in explicit bases. -/
noncomputable def gridDualMap (k : ℕ) :
    ∀ (n : ℕ) (r : ℤ), (gridComplex k n).X r ⟶ dual ((gridComplex k n).X ((n : ℤ) - r))
  | 0 => fun _ => ofMatrix (Matrix.of fun _ _ => 1)
  | n + 1 => basedDualProd (gridComplex k n) (circleComplex k) (circleComplex_dim_neg k) n 1
      ((n + 1 : ℕ) : ℤ) (by push_cast; ring) (gridDualMap k n) (circleB k)

end HSP.ChainModels
