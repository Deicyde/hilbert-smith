import Mathlib

/-!
# Signature splittings

For a real vector space `W`, a bilinear form `b` on `W` and a representation `ρ` of a monoid `G` on
`W`, a *signature splitting* is a pair of `ρ`-invariant subspaces `V⁺, V⁻` with `W = V⁺ ⊕ V⁻`
(complementary submodules), `b` positive definite on `V⁺` and negative definite on `V⁻`.
-/

namespace HSP

variable {G W : Type*} [AddCommGroup W] [Module ℝ W]

/-- `(V⁺, V⁻)` is a *signature splitting* of `(W, b, ρ)`: both subspaces are `ρ`-invariant, they
are complementary, `b` is positive definite on `V⁺` and negative definite on `V⁻`. -/
structure IsSignatureSplitting [Monoid G] (b : LinearMap.BilinForm ℝ W)
    (ρ : Representation ℝ G W) (Vp Vn : Submodule ℝ W) : Prop where
  /-- `V⁺` is invariant. -/
  mapsTo_pos : ∀ g, ∀ x ∈ Vp, ρ g x ∈ Vp
  /-- `V⁻` is invariant. -/
  mapsTo_neg : ∀ g, ∀ x ∈ Vn, ρ g x ∈ Vn
  /-- `W = V⁺ ⊕ V⁻`. -/
  isCompl : IsCompl Vp Vn
  /-- `b` is positive definite on `V⁺`. -/
  pos : ∀ x ∈ Vp, x ≠ 0 → 0 < b x x
  /-- `b` is negative definite on `V⁻`. -/
  neg : ∀ x ∈ Vn, x ≠ 0 → b x x < 0

end HSP
