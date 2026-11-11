import Mathlib

/-!
# Translates and thickenings of an invariant set

Let the `C_p`-action on `X` be isometric and `S ⊆ X` invariant. For `c ∈ C_p`, `c +ᵥ y` lies in the
open `ε`-thickening of `S` if and only if `y` does (`HSP.vadd_mem_thickening_iff`).
-/

open Metric

namespace HSP

variable {p : ℕ} {X : Type*} [MetricSpace X] [AddAction (ZMod p) X] [IsIsometricVAdd (ZMod p) X]

/-- For an invariant `S` and an isometric action, `c +ᵥ y` lies in the `ε`-thickening of `S` if
and only if `y` does. -/
theorem vadd_mem_thickening_iff {S : Set X} (hS : ∀ c : ZMod p, ∀ x ∈ S, c +ᵥ x ∈ S)
    (c : ZMod p) {ε : ℝ} {y : X} : c +ᵥ y ∈ thickening ε S ↔ y ∈ thickening ε S := by
  have key : ∀ (c : ZMod p) {y : X}, y ∈ thickening ε S → c +ᵥ y ∈ thickening ε S := by
    intro c y hy
    obtain ⟨z, hz, hd⟩ := mem_thickening_iff.1 hy
    exact mem_thickening_iff.2 ⟨c +ᵥ z, hS c z hz, by rwa [dist_vadd]⟩
  exact ⟨fun h => by simpa using key (-c) h, key c⟩

end HSP
