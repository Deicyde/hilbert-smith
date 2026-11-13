import Mathlib
import HilbertSmithPaper.Categories.Asymptotic.GroupSequence

/-!
# Standing data

The standing data of the corner chapter: a prime `p` (with `C_p = ZMod p` written additively), a
group sequence `G_i = ℤ/p^{a_i}` (`a_i ≥ 1`) with surjective `χ_i : G_i → C_p`, a nonempty compact
metric space `T` with a free isometric `C_p`-action, an integer `n ≥ 1` and reals `R > 0` and `s`
with `0 < s < R / √n`.

Lean encoding.
* The group sequence is determined by the exponents `a` and the homomorphisms `χ`:
  `HSP.Corner.StandingData.groupSeq` has `G_i = ZMod (p ^ a_i)`, so "`G_i = ℤ/p^{a_i}`" holds by
  definition rather than up to isomorphism. `q_i = |G_i|` is `StandingData.q`, and `N = n + 4` is
  `StandingData.N`.
* The `C_p`-action on `T` is an `AddAction (ZMod p) T` (written `c +ᵥ t`), isometric
  (`IsIsometricVAdd`), and free: `c +ᵥ t = t → c = 0`.
* The derived sets are the separate definitions `HSP.Corner.RoundSphere` with its round metric
  (from `n`), `HSP.Corner.exterior` (from `n` and `R`; `Z = T × Z₀` is
  `(Set.univ : Set T) ×ˢ exterior n R`) and the cut sets `HSP.Corner.cutB`, `cutY`, `cutA`, `yPlus`,
  `yMinus` (from `n` and `s`). On `T × S^n` Mathlib's product metric is the maximum metric, and
  `G_i` acts by `g • (t, z) = (χ_i(g) +ᵥ t, z)` (`GroupSeq.addAction` composed with the product
  action, `C_p` acting trivially on `S^n`).
-/

namespace HSP.Corner

/-- The *standing data*: a prime `p`; exponents `a_i ≥ 1` and surjections
`χ_i : ℤ/p^{a_i} → C_p = ZMod p`; a nonempty compact metric space `T` with a free isometric
`C_p`-action; an integer `n ≥ 1` and reals `R > 0` and `s` with `0 < s < R / √n`. -/
structure StandingData where
  /-- The prime `p`. -/
  p : ℕ
  /-- `p` is prime. -/
  [hp : Fact p.Prime]
  /-- The exponents `a_i`, with `G_i = ℤ/p^{a_i}`. -/
  a : ℕ → ℕ
  one_le_a : ∀ i, 1 ≤ a i
  /-- The homomorphisms `χ_i : G_i → C_p`. -/
  χ : ∀ i, ZMod (p ^ a i) →+ ZMod p
  χ_surjective : ∀ i, Function.Surjective (χ i)
  /-- The control space `T`. -/
  T : Type
  [metricSpace : MetricSpace T]
  [compactSpace : CompactSpace T]
  [nonempty : Nonempty T]
  /-- The action `(c, t) ↦ c +ᵥ t` of `C_p` on `T`. -/
  [addAction : AddAction (ZMod p) T]
  [isometric : IsIsometricVAdd (ZMod p) T]
  /-- The action is free. -/
  free : ∀ (c : ZMod p) (t : T), c +ᵥ t = t → c = 0
  /-- The dimension `n`. -/
  n : ℕ
  one_le_n : 1 ≤ n
  /-- The buffer radius `R`. -/
  R : ℝ
  /-- The cube size `s`. -/
  s : ℝ
  R_pos : 0 < R
  s_pos : 0 < s
  s_lt : s < R / √n

attribute [instance] StandingData.hp StandingData.metricSpace StandingData.compactSpace
  StandingData.nonempty StandingData.addAction StandingData.isometric

namespace StandingData

variable (D : StandingData)

/-- The group sequence `𝐆 = (ℤ/p^{a_i}, χ_i)` of the standing data. -/
def groupSeq : GroupSeq D.p where
  G i := ZMod (D.p ^ D.a i)
  fintype i := @ZMod.fintype (D.p ^ D.a i) ⟨pow_ne_zero _ D.hp.out.ne_zero⟩
  χ := D.χ

/-- `q_i = |G_i|`. -/
private def q (i : ℕ) : ℕ := Fintype.card (D.groupSeq.G i)

/-- `N = n + 4`. -/
def N : ℕ := D.n + 4

end StandingData

end HSP.Corner

/-! ### Non-vacuity witnesses (private)

Standing data from the toy control space `ZMod 2` (discrete metric, translation action),
`G_i = ℤ/2^{max(i,1)}` with reduction mod 2, `n = 1`, `R = 2`, `s = 1`. -/

section Witness
open HSP.Corner

/-- Toy control space: `ZMod 2` with the discrete metric. -/
private def Tw : Type := ZMod 2

private instance : DecidableEq Tw := inferInstanceAs (DecidableEq (ZMod 2))
private instance : Fintype Tw := inferInstanceAs (Fintype (ZMod 2))
private instance : AddAction (ZMod 2) Tw := inferInstanceAs (AddAction (ZMod 2) (ZMod 2))

private instance : MetricSpace Tw where
  dist x y := if x = y then 0 else 1
  dist_self x := by simp
  dist_comm x y := by by_cases h : x = y <;> simp [h, eq_comm]
  dist_triangle x y z := by
    by_cases h1 : x = y <;> by_cases h2 : y = z <;> by_cases h3 : x = z <;> simp_all
  eq_of_dist_eq_zero {x y} h := by by_contra h'; simp [h'] at h

private instance : IsIsometricVAdd (ZMod 2) Tw :=
  ⟨fun c => Isometry.of_dist_eq fun x y => by
    show (if c + (show ZMod 2 from x) = c + (show ZMod 2 from y) then (0:ℝ) else 1) = if (show ZMod 2 from x) = (show ZMod 2 from y) then 0 else 1
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd (add_left_cancel h1) h2
    · exact absurd (by rw [h2]) h1
    · rfl⟩

private def standingWitness : StandingData where
  p := 2
  hp := ⟨Nat.prime_two⟩
  a i := max i 1
  one_le_a i := le_max_right _ _
  χ i := (ZMod.castHom (dvd_pow_self 2 (by omega : max i 1 ≠ 0)) (ZMod 2)).toAddMonoidHom
  χ_surjective i := ZMod.ringHom_surjective _
  T := Tw
  nonempty := ⟨(0 : ZMod 2)⟩
  free c t h := by
    have h' : c + (show ZMod 2 from t) = 0 + (show ZMod 2 from t) := by rw [zero_add]; exact h
    exact add_right_cancel h'
  n := 1
  one_le_n := le_rfl
  R := 2
  s := 1
  R_pos := by norm_num
  s_pos := by norm_num
  s_lt := by norm_num


end Witness
