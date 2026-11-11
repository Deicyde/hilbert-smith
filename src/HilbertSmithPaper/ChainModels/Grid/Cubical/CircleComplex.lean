import Mathlib
import HilbertSmithPaper.ChainModels.Grid.Torus
import HilbertSmithPaper.LTheory.Localization.Products.BasedVectorSpaces

/-!
# The circle complex

The circle complex `S_k`: cells `[w]` in degree `0` and `e_w` in degree `1`, `w ∈ ℤ/k`, with
`d e_w = [w+1] - [w]`.

## Encoding

* `circleComplex k` (the declaration of the article) is `ChainComplex.of` of the dimensions
  `circleDim k` and the differential `circleD k`, whose matrix out of degree `1` is
  `circleDiffMatrix k` (`circleComplex_X`, `circleComplex_d` unfold it).
* `ℤ/k` is `Fin k`; the basis of `S_{k,0}` is `[0], …, [k-1]` and that of `S_{k,1}` is
  `e_0, …, e_{k-1}`.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP.ChainModels

open FreeQ

/-- The number of cells of `S_k` in degree `r`: `k` in degrees `0` and `1`, and `0` otherwise. -/
def circleDim (k : ℕ) : ℤ → ℕ
  | .ofNat 0 => k
  | .ofNat 1 => k
  | _ => 0

/-- The differential `d e_w = [w+1] - [w]` of `S_k`, as a `k × k` matrix (rows `[a]`, columns
`e_b`). -/
def circleDiffMatrix (k : ℕ) : Matrix (Fin k) (Fin k) ℚ :=
  Matrix.of fun a b =>
    (if (a : ℕ) = ((b : ℕ) + 1) % k then 1 else 0) - (if a = b then 1 else 0)

/-- The differential of `S_k` out of degree `n + 1`: the matrix above for `n = 0`, else `0`. -/
def circleD (k : ℕ) : ∀ n : ℤ, (⟨circleDim k (n + 1)⟩ : FreeQ) ⟶ ⟨circleDim k n⟩
  | .ofNat 0 => ofMatrix (circleDiffMatrix k)
  | .ofNat (_ + 1) => 0
  | .negSucc _ => 0

private lemma circleD_ne (k : ℕ) {n : ℤ} (h : n ≠ 0) : circleD k n = 0 := by
  rcases n with (_ | m) | m
  · exact absurd rfl h
  · rfl
  · rfl

/-- The *circle complex* `S_k`. -/
def circleComplex (k : ℕ) : ChainComplex FreeQ ℤ :=
  ChainComplex.of (fun r => ⟨circleDim k r⟩) (circleD k) fun n => by
    by_cases h : n = 0
    · subst h
      exact (congrArg (· ≫ circleD k 0) (circleD_ne k (show (0 : ℤ) + 1 ≠ 0 by decide))).trans
        zero_comp
    · rw [circleD_ne k h, comp_zero]

lemma circleComplex_X (k : ℕ) (r : ℤ) : (circleComplex k).X r = ⟨circleDim k r⟩ := rfl

lemma circleComplex_d (k : ℕ) : (circleComplex k).d 1 0 = ofMatrix (circleDiffMatrix k) :=
  ChainComplex.of_d (fun r => (⟨circleDim k r⟩ : FreeQ)) (circleD k) (0 : ℤ)

end HSP.ChainModels
