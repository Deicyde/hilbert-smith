import Mathlib
import HilbertSmithPaper.ChainModels.Grid.Torus
import HilbertSmithPaper.LTheory.Localization.Products.BasedVectorSpaces

/-!
# The circle complex

The circle complex `S_k`: cells `[w]` in degree `0` and `e_w` in degree `1`, `w ∈ ℤ/k`, with
`d e_w = [w+1] - [w]`; the realization of a cell is the point `4w/k` or the arc from `4w/k` to
`4(w+1)/k` of `ℝ/4ℤ`.

## Encoding

* `circleComplex k` (the declaration of the article) is `ChainComplex.of` of the dimensions
  `circleDim k` and the differential `circleD k`, whose matrix out of degree `1` is
  `circleDiffMatrix k` (`circleComplex_X`, `circleComplex_d` unfold it).
* `ℤ/k` is `Fin k`; a cell is a pair `(w, b) : Fin k × Bool`, `b = true` for `e_w`.
  `circleCell` reads a basis vector of `S_{k,r}` as a cell (in the order `[0], …, [k-1]` and
  `e_0, …, e_{k-1}`), and `cellRealization` is the realization of a cell.
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

/-- The cell `[w]` (for `r = 0`) or `e_w` (for `r = 1`) of the `w`-th basis vector of `S_{k,r}`. -/
def circleCell (k : ℕ) : ∀ r : ℤ, Fin ((circleComplex k).X r).dim → Fin k × Bool
  | .ofNat 0, w => (w, false)
  | .ofNat 1, w => (w, true)
  | .ofNat (_ + 2), w => w.elim0
  | .negSucc _, w => w.elim0

/-- The realization of a cell of `S_k`: the point `4w/k`, or the arc from `4w/k` to
`4(w+1)/k`. -/
def cellRealization (k : ℕ) (b : Fin k × Bool) : Set (AddCircle (4 : ℝ)) :=
  if b.2 then (fun t : ℝ => (t : AddCircle (4 : ℝ))) ''
      Set.Icc (4 * (b.1 : ℕ) / k : ℝ) (4 * ((b.1 : ℕ) + 1) / k)
  else {((4 * (b.1 : ℕ) / k : ℝ) : AddCircle (4 : ℝ))}

end HSP.ChainModels
