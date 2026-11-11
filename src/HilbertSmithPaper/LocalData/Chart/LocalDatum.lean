import Mathlib

/-!
# Local datum

A local datum with constants `(D, ρplus)` in dimension `n`: an open set `Ω ⊆ ℝⁿ` with a jointly
continuous action of `ℤ_[p]`, containing the ball of radius `2`, on which every point moves by at
most `D`, and with no point of norm at most `ρplus` fixed by all of `ℤ_[p]`.

## Encoding

* `ℝⁿ` is `EuclideanSpace ℝ (Fin n)`, so `‖·‖` and `dist` are Euclidean.
* `Ω` is a `Set` of `ℝⁿ` with an openness proof, and the action is an `AddAction ℤ_[p] Ω` on the
  subtype, jointly continuous in the sense of `ContinuousVAdd ℤ_[p] Ω` (subspace topology on `Ω`).
  Both are instance fields and are registered as instances, so for
  `A : LocalDatum p n D ρplus` and `x : A.Ω` one writes `a +ᵥ x : A.Ω`. Downstream definitions
  (the averaged map, the test regions as subsets of `A.Ω`, the restricted action on the test
  region, the control space as an orbit quotient) use this action directly; the test map extends
  maps on `A.Ω` to `OnePoint ℝⁿ`.
* The bounds `0 < D ≤ 1/64` and `0 < ρplus < 1/4` are fields, so a local datum exists only for
  such constants.
* The paper's `ρ₊` is written `ρplus` (a subscript `₊` is not an identifier character).
-/

namespace HSP

/-- A *local datum* with constants `(D, ρplus)` in dimension `n`: an open set `Ω ⊆ ℝⁿ` with a
jointly continuous action of `ℤ_[p]`, such that `B(0,2) ⊆ Ω`, `|a +ᵥ x - x| ≤ D` for all `a`
and `x`, and every `x ∈ Ω` with `|x| ≤ ρplus` is moved by some `a`. The constants satisfy
`0 < D ≤ 1/64` and `0 < ρplus < 1/4`. -/
structure LocalDatum (p : ℕ) [Fact p.Prime] (n : ℕ) (D ρplus : ℝ) where
  /-- The displacement bound is positive. -/
  D_pos : 0 < D
  /-- The displacement bound is at most `1/64`. -/
  D_le : D ≤ 1 / 64
  /-- The no-fixed-point radius is positive. -/
  ρplus_pos : 0 < ρplus
  /-- The no-fixed-point radius is less than `1/4`. -/
  ρplus_lt : ρplus < 1 / 4
  /-- The open domain `Ω ⊆ ℝⁿ`. -/
  Ω : Set (EuclideanSpace ℝ (Fin n))
  /-- `Ω` is open. -/
  isOpen_Ω : IsOpen Ω
  /-- The action of `ℤ_[p]` on `Ω`. -/
  [act : AddAction ℤ_[p] Ω]
  /-- The action is jointly continuous. -/
  [continuousVAdd : ContinuousVAdd ℤ_[p] Ω]
  /-- Containment: `B(0,2) ⊆ Ω`. -/
  ball_subset : Metric.ball 0 2 ⊆ Ω
  /-- Displacement: every point moves by at most `D`. -/
  dist_vadd_le : ∀ (a : ℤ_[p]) (x : Ω), dist ((a +ᵥ x : Ω) : EuclideanSpace ℝ (Fin n)) x ≤ D
  /-- No fixed points near the origin. -/
  exists_moved : ∀ x : Ω, ‖(x : EuclideanSpace ℝ (Fin n))‖ ≤ ρplus → ∃ a : ℤ_[p], a +ᵥ x ≠ x

attribute [instance] LocalDatum.act LocalDatum.continuousVAdd

end HSP
