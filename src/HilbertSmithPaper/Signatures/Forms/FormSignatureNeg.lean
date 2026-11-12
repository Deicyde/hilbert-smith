import Mathlib
import HilbertSmithPaper.Signatures.Forms.SignatureSplitting
import HilbertSmithPaper.Signatures.LFour.SignatureSplittingIndependence

/-!
# Negation

`sign_{-b} = -sign_b`: a signature splitting `(V⁺, V⁻)` of `b` gives the splitting `(V⁻, V⁺)` of
`-b`, and conversely, so both sides come from independence, or both are `0` when there is no
splitting.
-/

namespace HSP

open Module

variable {G W : Type*} [Monoid G] [AddCommGroup W] [Module ℝ W]

/-- Swapping the pieces of a splitting of `b` gives a splitting of `-b`. -/
private lemma IsSignatureSplitting.neg_swap {b : LinearMap.BilinForm ℝ W}
    {ρ : Representation ℝ G W} {Vp Vn : Submodule ℝ W} (h : IsSignatureSplitting b ρ Vp Vn) :
    IsSignatureSplitting (-b) ρ Vn Vp where
  mapsTo_pos := h.mapsTo_neg
  mapsTo_neg := h.mapsTo_pos
  isCompl := h.isCompl.symm
  pos x hx h0 := by simpa using h.neg x hx h0
  neg x hx h0 := by simpa using h.pos x hx h0

/-- **Negation.** `sign_{-b} = -sign_b`. -/
theorem formSign_neg [FiniteDimensional ℝ W] (b : LinearMap.BilinForm ℝ W)
    (ρ : Representation ℝ G W) (g : G) : formSign (-b) ρ g = -formSign b ρ g := by
  by_cases h : ∃ Vp Vn : Submodule ℝ W, IsSignatureSplitting b ρ Vp Vn
  · obtain ⟨Vp, Vn, h⟩ := h
    rw [formSign_eq_of_splitting h.neg_swap g, formSign_eq_of_splitting h g]
    ring
  · have h' : ¬ ∃ Vp Vn : Submodule ℝ W, IsSignatureSplitting (-b) ρ Vp Vn := by
      rintro ⟨Vp, Vn, h'⟩
      exact h ⟨Vn, Vp, neg_neg b ▸ h'.neg_swap⟩
    simp [formSign, h, h']

end HSP
