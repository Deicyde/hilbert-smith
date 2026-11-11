import Mathlib
import HilbertSmithPaper.Signatures.Forms.SignatureSplitting
import HilbertSmithPaper.Signatures.LFour.SignatureSplittingExists
import HilbertSmithPaper.Signatures.LFour.SignatureSplittingIndependence

/-!
# Value at the identity

For every decomposition `W = V⁺ ⊕ V⁻` with `b` positive definite on `V⁺` and negative definite on
`V⁻` (invariant or not), `sign_b 1 = dim V⁺ - dim V⁻`. In particular this integer does not depend
on `G` or `ρ`.

The trace of the identity is the dimension. Independence for `G`, applied to a `ρ`-invariant
splitting (which exists), computes `sign_b 1`; independence for the trivial group, for which every
such decomposition is a signature splitting, shows that `dim V⁺ - dim V⁻` is the same for all of
them.
-/

namespace HSP

open Module

variable {G W : Type*} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]

/-- The trace of a restriction of the identity is the dimension. -/
private lemma trace_restrict_eq_finrank {f : W →ₗ[ℝ] W} (hf : f = 1) {V : Submodule ℝ W}
    (hV : ∀ x ∈ V, f x ∈ V) : LinearMap.trace ℝ V (f.restrict hV) = finrank ℝ V := by
  subst hf
  rw [← LinearMap.trace_one]
  congr 1

/-- `dim V⁺ - dim V⁻` for any signature splitting, through independence. -/
private lemma formSign_one_eq {M : Type*} [Monoid M] {b : LinearMap.BilinForm ℝ W}
    {ρ : Representation ℝ M W} {Vp Vn : Submodule ℝ W} (h : IsSignatureSplitting b ρ Vp Vn) :
    formSign b ρ 1 = finrank ℝ Vp - finrank ℝ Vn := by
  rw [formSign_eq_of_splitting h, trace_restrict_eq_finrank (map_one ρ),
    trace_restrict_eq_finrank (map_one ρ)]

/-- **Value at the identity.** For every decomposition `W = V⁺ ⊕ V⁻` with `b` positive definite
on `V⁺` and negative definite on `V⁻`, `sign_b 1 = dim V⁺ - dim V⁻`. -/
theorem formSign_one [Group G] [Finite G] {b : LinearMap.BilinForm ℝ W}
    {ρ : Representation ℝ G W} (hb : b.IsSymm) (hnd : b.Nondegenerate)
    (hρ : ∀ g x y, b (ρ g x) (ρ g y) = b x y) {Vp Vn : Submodule ℝ W} (hc : IsCompl Vp Vn)
    (hp : ∀ x ∈ Vp, x ≠ 0 → 0 < b x x) (hn : ∀ x ∈ Vn, x ≠ 0 → b x x < 0) :
    formSign b ρ 1 = (((finrank ℝ Vp : ℤ) - finrank ℝ Vn : ℤ) : ℝ) := by
  obtain ⟨Up, Un, hU⟩ := exists_signatureSplitting b ρ hb hnd hρ
  let ρ₀ : Representation ℝ Unit W := 1
  have hU₀ : IsSignatureSplitting b ρ₀ Up Un :=
    ⟨fun _ x hx => by simpa [ρ₀] using hx, fun _ x hx => by simpa [ρ₀] using hx, hU.isCompl,
      hU.pos, hU.neg⟩
  have hV₀ : IsSignatureSplitting b ρ₀ Vp Vn :=
    ⟨fun _ x hx => by simpa [ρ₀] using hx, fun _ x hx => by simpa [ρ₀] using hx, hc, hp, hn⟩
  have := (formSign_one_eq hU₀).symm.trans (formSign_one_eq hV₀)
  rw [formSign_one_eq hU, this]
  push_cast
  ring

end HSP
