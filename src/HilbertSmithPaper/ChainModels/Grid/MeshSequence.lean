import Mathlib
import HilbertSmithPaper.ChainModels.Approximations.Modulus
import HilbertSmithPaper.ChainModels.Mesh.MeshStart
import HilbertSmithPaper.ChainModels.Approximations.CompletedMapsProperties

/-!
# Mesh sequence

`k₀` is the least integer `k₀ ≥ 8` with `3ω(2h₀) + 8h₀ ≤ 1/16`, `h₀ = 4/k₀`, for the modulus `ω`
of the track family; `k_i = k₀ + i` and `h_i = 4/k_i`. Such `k₀` exists because `ω(t) → 0` as
`t → 0`; the inequality then holds for every `h_i` because `ω` is nondecreasing, and in
particular `h_i ≤ 1/128`.

## Encoding

`meshSequence A i` is `k_i = meshStart A + i` (the declaration of the article), with `k₀` the
mesh start. The monotonicity facts come from the properties of completed maps, applied with the
pinch radius `ρ₊/2` (the modulus does not involve `ρ`).
-/

namespace HSP.ChainModels

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- The *mesh sequence* `k_i = k₀ + i`; the mesh is `h_i = 4/k_i`. -/
noncomputable def meshSequence (A : LocalDatum p n D ρplus) (i : ℕ) : ℕ :=
  meshStart A + i

/-- `k_i ≥ 8`. -/
lemma eight_le_meshSequence (A : LocalDatum p n D ρplus) (i : ℕ) : 8 ≤ meshSequence A i := by
  exact (meshStart_spec A).1.trans (Nat.le_add_right _ _)

/-- `3ω(2h_i) + 8h_i ≤ 1/16` for every `i`. -/
lemma meshSequence_spec (A : LocalDatum p n D ρplus) (i : ℕ) :
    3 * trackModulus A (2 * (4 / (meshSequence A i : ℝ))) + 8 * (4 / (meshSequence A i : ℝ)) ≤
      1 / 16 := by
  have hmono := (completedMaps_properties A (half_pos A.ρplus_pos)
    (half_lt_self A.ρplus_pos)).1.1
  have h0 := (meshStart_spec A).2
  have hk0 : (8 : ℝ) ≤ meshStart A := by exact_mod_cast (meshStart_spec A).1
  have hle : 4 / (meshSequence A i : ℝ) ≤ 4 / (meshStart A : ℝ) := by
    unfold meshSequence
    exact div_le_div_of_nonneg_left (by norm_num) (by linarith) (by push_cast; linarith)
  have := hmono (mul_le_mul_of_nonneg_left hle zero_le_two)
  linarith

/-- In particular `h_i ≤ 1/128`. -/
lemma meshSequence_mesh_le (A : LocalDatum p n D ρplus) (i : ℕ) :
    4 / (meshSequence A i : ℝ) ≤ 1 / 128 := by
  have hspec := meshSequence_spec A i
  have hpos : 0 ≤ 4 / (meshSequence A i : ℝ) := by positivity
  have hω := (completedMaps_properties A (half_pos A.ρplus_pos)
    (half_lt_self A.ρplus_pos)).1.2.1 (2 * (4 / (meshSequence A i : ℝ)))
  linarith

end HSP.ChainModels
