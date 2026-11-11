import Mathlib
import HilbertSmithPaper.ChainModels.Grid.GridBox

/-!
# Boxes are acyclic

Every grid box `B ⊆ C(k)` is augmented acyclic: `H_r(B) = 0` for `r > 0`, and `ε` induces
`H_0(B) ≅ ℚ`.

## Encoding

* Chains of `C(k)_r` are columns `Fin dim → ℚ`, and `d`, `ε` act by `Matrix.mulVec`.
* `cubeSpan S r` is the span in `C(k)_r` of the basis cubes in `S`: the columns vanishing off
  `S`. For `S = B.cubes` it is the degree-`r` part of the subcomplex `B`.
* Augmented acyclicity is spelled out on elements, as for carriers: every cycle of positive
  degree in `B` bounds in `B`; a degree-`0` chain of `B` with augmentation `0` bounds in `B`
  (injectivity of `H_0(B) → ℚ`); some degree-`0` chain of `B` has augmentation `1`
  (surjectivity). Every degree-`0` chain is a cycle, as `C(k)_{-1} = 0`.
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

/-- **Boxes are acyclic.** Every grid box `B` is augmented acyclic: `H_r(B) = 0` for `r > 0`,
and `ε` induces `H_0(B) ≅ ℚ`. -/
theorem box_acyclic {k n : ℕ} (B : GridBox k n) :
    (∀ s : ℤ, 0 < s → ∀ z ∈ cubeSpan B.cubes s,
      toMatrix ((gridComplex k n).d s (s - 1)) *ᵥ z = 0 →
      ∃ y ∈ cubeSpan B.cubes (s + 1), toMatrix ((gridComplex k n).d (s + 1) s) *ᵥ y = z) ∧
    (∀ z ∈ cubeSpan B.cubes 0, toMatrix (gridAug k n) *ᵥ z = 0 →
      ∃ y ∈ cubeSpan B.cubes 1, toMatrix ((gridComplex k n).d 1 0) *ᵥ y = z) ∧
    (∃ z ∈ cubeSpan B.cubes 0, toMatrix (gridAug k n) *ᵥ z = fun _ => 1) := by
  sorry

end HSP.ChainModels
