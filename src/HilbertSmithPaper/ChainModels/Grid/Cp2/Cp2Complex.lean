import Mathlib
import HilbertSmithPaper.LTheory.Localization.Products.BasedVectorSpaces

/-!
# The cellular chain complex of `CP²`

`P_r = ℚ e_r` for `r ∈ {0, 2, 4}`, zero otherwise, with zero differential.

## Encoding

`cp2Complex` (the declaration of the article) is `ChainComplex.of` with `P_r = ⟨cp2Dim r⟩`;
`cp2Dim_eq` and `cp2Complex_d` unfold the dimensions and the zero differential.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP.ChainModels

open FreeQ DualCat

/-- The number of cells of `CP²` in degree `r`: `1` for `r ∈ {0, 2, 4}`, else `0`. -/
def cp2Dim : ℤ → ℕ
  | .ofNat 0 => 1
  | .ofNat 2 => 1
  | .ofNat 4 => 1
  | _ => 0

lemma cp2Dim_eq (r : ℤ) : cp2Dim r = if r = 0 ∨ r = 2 ∨ r = 4 then 1 else 0 :=
  match r with
  | .ofNat 0 => rfl
  | .ofNat 1 => rfl
  | .ofNat 2 => rfl
  | .ofNat 3 => rfl
  | .ofNat 4 => rfl
  | .ofNat (n + 5) => by
    show 0 = _
    rw [eq_comm, ite_eq_right_iff]
    intro h
    simp only [Int.ofNat_eq_natCast] at h
    omega
  | .negSucc n => by
    show 0 = _
    rw [eq_comm, ite_eq_right_iff]
    intro h
    rw [Int.negSucc_eq] at h
    omega

/-- The cellular chain complex `P` of `CP²`, with zero differential. -/
def cp2Complex : ChainComplex FreeQ ℤ :=
  ChainComplex.of (fun r => ⟨cp2Dim r⟩) (fun _ => 0) fun _ => zero_comp

lemma cp2Complex_d (i j : ℤ) : cp2Complex.d i j = 0 := by
  show ChainComplex.of.d (fun r => (⟨cp2Dim r⟩ : FreeQ)) (fun _ => 0) i j = 0
  unfold ChainComplex.of.d
  split_ifs <;> simp

end HSP.ChainModels
