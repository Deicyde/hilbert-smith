import Mathlib
import HilbertSmithPaper.Signatures.LFour.SignatureSplittingExists

/-!
# The equivariant signature of an invariant form

For a bilinear form `b` on a real vector space `W` and a representation `ρ` of `G` on `W`, fix a
signature splitting `(V⁺, V⁻)` (chosen by `Classical.choose`) and set
`sign_b g = tr (ρ g | V⁺) - tr (ρ g | V⁻)`.

The definition is total: when `(W, b, ρ)` has no signature splitting the value is `0`. By the
existence lemma this never happens for a nondegenerate symmetric invariant form under a finite
group, which is the case the paper uses.
-/

namespace HSP

open Module

variable {G W : Type*} [Monoid G] [AddCommGroup W] [Module ℝ W]

open Classical in
/-- The *equivariant signature* `sign_b : G → ℝ` of `b` with respect to `ρ`: the difference of the
traces of `ρ g` on the two pieces of a chosen signature splitting, and `0` if there is none. -/
noncomputable def formSign (b : LinearMap.BilinForm ℝ W) (ρ : Representation ℝ G W) (g : G) : ℝ :=
  if h : ∃ Vp Vn : Submodule ℝ W, IsSignatureSplitting b ρ Vp Vn then
    LinearMap.trace ℝ _ ((ρ g).restrict (h.choose_spec.choose_spec.mapsTo_pos g)) -
      LinearMap.trace ℝ _ ((ρ g).restrict (h.choose_spec.choose_spec.mapsTo_neg g))
  else 0

end HSP
