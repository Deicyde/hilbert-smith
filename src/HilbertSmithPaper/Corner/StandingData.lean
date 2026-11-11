import Mathlib
import HilbertSmithPaper.Categories.Asymptotic.GroupSequence
import HilbertSmithPaper.Corner.RoundSphere
import HilbertSmithPaper.Corner.Exterior
import HilbertSmithPaper.Corner.CutSets

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
def q (i : ℕ) : ℕ := Fintype.card (D.groupSeq.G i)

/-- `N = n + 4`. -/
def N : ℕ := D.n + 4

end StandingData

end HSP.Corner
