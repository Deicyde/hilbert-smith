import Mathlib

/-!
# Graph-type matrices

Let `X` be a metric space with an action `(c, x) ↦ c +ᵥ x` of `C_p = ZMod p`, written additively.
A rational matrix `u ∈ ℚ^{B' × B}` between finite based `ℚ`-modules whose basis elements carry
labels `l : B → X`, `l' : B' → X` has *graph type `c` with bound `δ`* if every nonzero entry
`u b' b` satisfies `d(l' b', c +ᵥ l b) ≤ δ`.

Lean encoding. `HSP.Corner.IsGraphType l l' c δ u` is a `Prop` on a `Matrix B' B ℚ` with label
maps. The definition needs neither isometry of the action, finiteness of the bases nor `δ ≥ 0`;
these belong to the setting in which it is used (the calculus of graph types). For `X = T × S^n` with
labels `(t_b, z_b)`, Mathlib's maximum metric on the product and the trivial action on `S^n` give
`d_T(t_{b'}, c +ᵥ t_b) ≤ δ` and `d_S(z_{b'}, z_b) ≤ δ`; type `0` with bound `δ` is propagation at
most `δ`.
-/

namespace HSP.Corner

variable {p : ℕ} {X : Type*} [MetricSpace X] [AddAction (ZMod p) X] {B B' : Type*}

/-- A matrix `u ∈ ℚ^{B' × B}` with source labels `l` and target labels `l'` has *graph type `c`
with bound `δ`* if every nonzero entry `u b' b` satisfies `d(l' b', c +ᵥ l b) ≤ δ`. -/
def IsGraphType (l : B → X) (l' : B' → X) (c : ZMod p) (δ : ℝ) (u : Matrix B' B ℚ) : Prop :=
  ∀ b' b, u b' b ≠ 0 → dist (l' b') (c +ᵥ l b) ≤ δ

end HSP.Corner

/-! ### Non-vacuity witnesses (private)

A graph-type matrix over the toy space `ZMod 2` (discrete metric, translation action). -/

section Witness
open HSP.Corner

/-- Toy space: `ZMod 2` with the discrete metric. -/
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

private theorem graphTypeWitness :
    IsGraphType (p := 2) (fun _ : Fin 1 => (show Tw from (0 : ZMod 2))) (fun _ : Fin 1 => ((1 : ZMod 2) +ᵥ (show Tw from (0 : ZMod 2))))
      1 0 (1 : Matrix (Fin 1) (Fin 1) ℚ) := by
  intro b' b _; exact (dist_self _).le

end Witness
