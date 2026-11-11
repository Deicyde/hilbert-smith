import Mathlib
import HilbertSmithPaper.Corner.Actions.GraphType

/-!
# Exterior witnesses

Let `X` be a metric space with a `C_p`-action and `Z ⊆ X`. A matrix `e : M → M'` is an *exterior
witness of type `c` with bound `δ`* if `e = x y` with `y : M → W` and `x : W → M'` through a finite
labelled based module `W` all of whose labels lie within `δ` of `Z`, `y` of graph type `0` and `x` of
graph type `c`, both with bound `δ`.

Lean encoding. The basis of `W` is `Fin k` for some `k : ℕ` (every finite basis is in bijection with
one), with labels `μ : Fin k → X`; "within `δ` of `Z`" is `∃ z ∈ Z, d(μ w, z) ≤ δ` (so that no label
is within `δ` of the empty set). The definition does not need `Z` closed and invariant; those are
hypotheses of the lemmas about witnesses.
-/

namespace HSP.Corner

variable {p : ℕ} {X : Type*} [MetricSpace X] [AddAction (ZMod p) X] {B B' : Type*}

/-- `e ∈ ℚ^{B' × B}` (labels `l` on `B`, `l'` on `B'`) is an *exterior witness of type `c` with
bound `δ`* for `Z ⊆ X` if `e = x * y` through a finite labelled basis `W = Fin k` with labels `μ`
each within `δ` of `Z`, where `y` has graph type `0` and `x` graph type `c`, both with bound `δ`. -/
def IsExteriorWitness (Z : Set X) (l : B → X) (l' : B' → X) (c : ZMod p) (δ : ℝ)
    (e : Matrix B' B ℚ) : Prop :=
  ∃ (k : ℕ) (μ : Fin k → X) (x : Matrix B' (Fin k) ℚ) (y : Matrix (Fin k) B ℚ),
    e = x * y ∧ (∀ w, ∃ z ∈ Z, dist (μ w) z ≤ δ) ∧
      IsGraphType l μ (0 : ZMod p) δ y ∧ IsGraphType μ l' c δ x

end HSP.Corner
