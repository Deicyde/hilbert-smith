import Mathlib
import HilbertSmithPaper.Signatures.Forms.FormSignature

/-!
# The signature does not depend on the splitting

For any signature splitting `(V'⁺, V'⁻)` of `(W, b, ρ)`, the equivariant signature `sign_b g` is
`tr (ρ g | V'⁺) - tr (ρ g | V'⁻)`.

Sylvester's argument: a positive definite and a negative definite subspace meet in `0`, so the
two positive parts have equal dimension, and the projection along the chosen `V⁻` restricts to an
equivariant isomorphism `V'⁺ ≃ V⁺`; the traces agree by conjugation invariance. Likewise for the
negative parts. The argument needs neither symmetry nor nondegeneracy of `b`, nor finiteness of
`G`: only the splitting itself.
-/

namespace HSP

open Module

variable {G W : Type*} [Monoid G] [AddCommGroup W] [Module ℝ W]

/-- A subspace where `b` is positive definite meets one where it is negative definite in `0`. -/
private lemma disjoint_of_pos_neg {b : LinearMap.BilinForm ℝ W} {U N : Submodule ℝ W}
    (hU : ∀ x ∈ U, x ≠ 0 → 0 < b x x) (hN : ∀ x ∈ N, x ≠ 0 → b x x < 0) : Disjoint U N := by
  rw [Submodule.disjoint_def]
  intro x hxU hxN
  by_contra hx
  linarith [hU x hxU hx, hN x hxN hx]

variable [FiniteDimensional ℝ W]

/-- A subspace disjoint from `N` is at most as large as a complement of `N`. -/
private lemma finrank_le_of_disjoint {U V N : Submodule ℝ W} (hVN : IsCompl V N)
    (hUN : Disjoint U N) : finrank ℝ U ≤ finrank ℝ V := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq U N
  have h2 := Submodule.finrank_add_eq_of_isCompl hVN
  have h3 := Submodule.finrank_le (U ⊔ N)
  rw [hUN.eq_bot, finrank_bot] at h1
  omega

/-- If `U` is disjoint from `N`, `V` is a complement of `N`, all three are invariant, and `U`, `V`
have equal dimension, then `ρ g` has the same trace on `U` and on `V`. -/
private lemma trace_eq_of_disjoint {ρ : Representation ℝ G W} {U V N : Submodule ℝ W}
    (hU : ∀ g, ∀ x ∈ U, ρ g x ∈ U) (hV : ∀ g, ∀ x ∈ V, ρ g x ∈ V)
    (hN : ∀ g, ∀ x ∈ N, ρ g x ∈ N) (hVN : IsCompl V N) (hUN : Disjoint U N)
    (hdim : finrank ℝ U = finrank ℝ V) (g : G) :
    LinearMap.trace ℝ U ((ρ g).restrict (hU g)) = LinearMap.trace ℝ V ((ρ g).restrict (hV g)) := by
  set π : W →ₗ[ℝ] V := Submodule.projectionOnto V N hVN
  have hπ : ∀ x : W, π (ρ g x) = ⟨ρ g (π x), hV g _ (π x).2⟩ := by
    intro x
    have hx : x = (π x : W) + (x - π x) := by abel
    have hxN : x - π x ∈ N := by
      simpa [π, Submodule.coe_projectionOnto_apply] using Submodule.sub_projection_mem hVN x
    conv_lhs => rw [hx, map_add, map_add]
    rw [Submodule.projectionOnto_apply_of_mem_left hVN (hV g _ (π x).2),
      (Submodule.projectionOnto_apply_eq_zero_iff hVN).2 (hN g _ hxN), add_zero]
  have hinj : Function.Injective (π ∘ₗ U.subtype) := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.projectionOnto_apply_eq_zero_iff] at hx
    have : (x : W) = 0 := (Submodule.disjoint_def.1 hUN) x x.2 hx
    simpa [Submodule.mem_bot] using Subtype.ext this
  set e : U ≃ₗ[ℝ] V := LinearMap.linearEquivOfInjective _ hinj hdim
  rw [← LinearMap.trace_conj' ((ρ g).restrict (hU g)) e]
  congr 1
  ext y
  obtain ⟨u, rfl⟩ := e.surjective y
  simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]
  change ((π (ρ g u) : V) : W) = ρ g ((π u : V) : W)
  rw [hπ]

/-- **The signature does not depend on the splitting.** For any signature splitting
`(V'⁺, V'⁻)` of `(W, b, ρ)`, `sign_b g = tr (ρ g | V'⁺) - tr (ρ g | V'⁻)`. -/
theorem formSign_eq_of_splitting {b : LinearMap.BilinForm ℝ W} {ρ : Representation ℝ G W}
    {Up Un : Submodule ℝ W} (h : IsSignatureSplitting b ρ Up Un) (g : G) :
    formSign b ρ g = LinearMap.trace ℝ Up ((ρ g).restrict (h.mapsTo_pos g)) -
      LinearMap.trace ℝ Un ((ρ g).restrict (h.mapsTo_neg g)) := by
  have hex : ∃ Vp Vn : Submodule ℝ W, IsSignatureSplitting b ρ Vp Vn := ⟨Up, Un, h⟩
  rw [formSign, dite_eq_left hex]
  have hV := hex.choose_spec.choose_spec
  have d1 := disjoint_of_pos_neg h.pos hV.neg
  have d2 := disjoint_of_pos_neg hV.pos h.neg
  have d3 := disjoint_of_pos_neg hV.pos h.neg |>.symm
  have d4 := disjoint_of_pos_neg h.pos hV.neg |>.symm
  have hp : finrank ℝ Up = finrank ℝ hex.choose :=
    le_antisymm (finrank_le_of_disjoint hV.isCompl d1) (finrank_le_of_disjoint h.isCompl d2)
  have hn : finrank ℝ Un = finrank ℝ hex.choose_spec.choose :=
    le_antisymm (finrank_le_of_disjoint hV.isCompl.symm d3)
      (finrank_le_of_disjoint h.isCompl.symm d4)
  rw [trace_eq_of_disjoint h.mapsTo_pos hV.mapsTo_pos hV.mapsTo_neg hV.isCompl d1 hp g,
    trace_eq_of_disjoint h.mapsTo_neg hV.mapsTo_neg hV.mapsTo_pos hV.isCompl.symm d3 hn g]

end HSP
