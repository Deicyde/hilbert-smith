import Mathlib

/-!
# Invariant signature splittings exist

Let `W` be a finite-dimensional real vector space, `b` a nondegenerate symmetric bilinear form on
`W`, and `ρ` a representation of a finite group `G` on `W` by `b`-isometries. A *signature
splitting* is a pair of `ρ`-invariant subspaces `V⁺, V⁻` with `W = V⁺ ⊕ V⁻` (complementary
submodules), `b` positive definite on `V⁺` and negative definite on `V⁻`. Such a splitting exists.

The predicate `IsSignatureSplitting` is stated for any bilinear form and any representation of a
monoid; the hypotheses on `b` and `G` are only needed for existence.
-/

namespace HSP

open Module

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

/-- **Invariant signature splittings exist.** A nondegenerate symmetric bilinear form on a
finite-dimensional real vector space, invariant under a representation of a finite group, has a
signature splitting. -/
theorem exists_signatureSplitting [Group G] [Finite G] [FiniteDimensional ℝ W]
    (b : LinearMap.BilinForm ℝ W) (ρ : Representation ℝ G W) (hb : b.IsSymm)
    (hnd : b.Nondegenerate) (hρ : ∀ g x y, b (ρ g x) (ρ g y) = b x y) :
    ∃ Vp Vn : Submodule ℝ W, IsSignatureSplitting b ρ Vp Vn := by
  sorry

end HSP
