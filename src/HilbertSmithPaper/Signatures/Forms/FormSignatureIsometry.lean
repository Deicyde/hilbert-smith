import Mathlib
import HilbertSmithPaper.Signatures.LFour.SignatureSplittingIndependence

/-!
# Isometry invariance

If `e : W ≃ W'` is a `G`-equivariant isometric isomorphism from `b` to `b'`, then
`sign_b = sign_{b'}`. A splitting `(V⁺, V⁻)` of `W` is carried to the splitting `(e V⁺, e V⁻)` of
`W'`, on whose pieces `ρ' g` is conjugate to `ρ g` along `e`; if `W` has no splitting, neither
has `W'` (transport back along `e⁻¹`), and both signatures are `0`.
-/

namespace HSP

open Module

variable {G W W' : Type*} [Monoid G] [AddCommGroup W] [Module ℝ W] [AddCommGroup W']
  [Module ℝ W']

/-- Transport of a signature splitting along an equivariant isometry. -/
private lemma IsSignatureSplitting.map {b : LinearMap.BilinForm ℝ W}
    {b' : LinearMap.BilinForm ℝ W'} {ρ : Representation ℝ G W} {ρ' : Representation ℝ G W'}
    (e : W ≃ₗ[ℝ] W') (he : ∀ x y, b' (e x) (e y) = b x y) (hρ : ∀ g x, e (ρ g x) = ρ' g (e x))
    {Vp Vn : Submodule ℝ W} (h : IsSignatureSplitting b ρ Vp Vn) :
    IsSignatureSplitting b' ρ' (Vp.map e.toLinearMap) (Vn.map e.toLinearMap) where
  mapsTo_pos g x hx := by
    obtain ⟨u, hu, rfl⟩ := hx
    exact ⟨ρ g u, h.mapsTo_pos g u hu, hρ g u⟩
  mapsTo_neg g x hx := by
    obtain ⟨u, hu, rfl⟩ := hx
    exact ⟨ρ g u, h.mapsTo_neg g u hu, hρ g u⟩
  isCompl := Submodule.isCompl_map e h.isCompl
  pos x hx h0 := by
    obtain ⟨u, hu, rfl⟩ := hx
    rw [LinearEquiv.coe_coe, he]
    exact h.pos u hu (by rintro rfl; simp at h0)
  neg x hx h0 := by
    obtain ⟨u, hu, rfl⟩ := hx
    rw [LinearEquiv.coe_coe, he]
    exact h.neg u hu (by rintro rfl; simp at h0)

/-- The trace of `ρ' g` on `e V` equals that of `ρ g` on `V`. -/
private lemma trace_restrict_map {ρ : Representation ℝ G W} {ρ' : Representation ℝ G W'}
    (e : W ≃ₗ[ℝ] W') (hρ : ∀ g x, e (ρ g x) = ρ' g (e x)) {V : Submodule ℝ W} (g : G)
    (hV : ∀ x ∈ V, ρ g x ∈ V) (hV' : ∀ x ∈ V.map e.toLinearMap, ρ' g x ∈ V.map e.toLinearMap) :
    LinearMap.trace ℝ _ ((ρ' g).restrict hV') = LinearMap.trace ℝ V ((ρ g).restrict hV) := by
  rw [← LinearMap.trace_conj' ((ρ g).restrict hV) (e.submoduleMap V)]
  congr 1
  ext y
  obtain ⟨u, rfl⟩ := (e.submoduleMap V).surjective y
  simp [LinearEquiv.conj_apply, hρ]

/-- **Isometry invariance.** A `G`-equivariant isometric isomorphism `e` from `b` to `b'` gives
`sign_b = sign_{b'}`. -/
theorem formSign_congr [FiniteDimensional ℝ W] {b : LinearMap.BilinForm ℝ W}
    {b' : LinearMap.BilinForm ℝ W'} {ρ : Representation ℝ G W} {ρ' : Representation ℝ G W'}
    (e : W ≃ₗ[ℝ] W') (he : ∀ x y, b' (e x) (e y) = b x y) (hρ : ∀ g x, e (ρ g x) = ρ' g (e x)) :
    formSign b ρ = formSign b' ρ' := by
  have : FiniteDimensional ℝ W' := e.finiteDimensional
  have he' : ∀ x y, b (e.symm x) (e.symm y) = b' x y := fun x y => by
    rw [← he, e.apply_symm_apply, e.apply_symm_apply]
  have hρ' : ∀ g x, e.symm (ρ' g x) = ρ g (e.symm x) := fun g x => by
    apply e.injective
    rw [e.apply_symm_apply, hρ, e.apply_symm_apply]
  funext g
  by_cases h : ∃ Vp Vn : Submodule ℝ W, IsSignatureSplitting b ρ Vp Vn
  · obtain ⟨Vp, Vn, h⟩ := h
    rw [formSign_eq_of_splitting h g, formSign_eq_of_splitting (h.map e he hρ) g,
      trace_restrict_map e hρ g, trace_restrict_map e hρ g]
  · have h' : ¬ ∃ Vp Vn : Submodule ℝ W', IsSignatureSplitting b' ρ' Vp Vn := by
      rintro ⟨Vp, Vn, h'⟩
      exact h ⟨_, _, h'.map e.symm he' hρ'⟩
    simp [formSign, h, h']

end HSP
