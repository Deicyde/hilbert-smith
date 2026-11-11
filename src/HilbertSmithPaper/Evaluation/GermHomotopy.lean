import HilbertSmithPaper.Evaluation.Germ

/-!
# Homotopic labellings have equal classes

If `c₀, c₁ : 𝕋ⁿ → Sⁿ` are homotopic, then `𝔪_{c₀} = 𝔪_{c₁}` for the labelled-model class.
-/

open HSP.ChainModels

namespace HSP.Evaluation

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- Homotopic labellings `c₀ ≃ c₁` have equal labelled-model classes `𝔪_{c₀} = 𝔪_{c₁}`. -/
theorem germ_eq_of_homotopic (A : LocalDatum p n D ρplus) (R : ℝ)
    {c₀ c₁ : C(Torus n, Corner.RoundSphere n)} (h : ContinuousMap.Homotopic c₀ c₁) :
    germ A R c₀ = germ A R c₁ := by
  sorry

end HSP.Evaluation
