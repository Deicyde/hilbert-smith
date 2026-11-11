import Mathlib
import HilbertSmithPaper.LocalData.Control.ControlMetric
import HilbertSmithPaper.LocalData.Chart.TestRegionCompact

/-!
# The orbit map is uniformly continuous

For `ε > 0` there is `δ > 0` with `d_T (π z) (π w) < ε` whenever `z, w ∈ Z⁺` and `|z - w| < δ`.
The map `(a, z) ↦ a +ᵥ z` is uniformly continuous on the compact `ℤ_[p] × Z⁺` (Heine–Cantor), so
`d₁ z w ≤ ε / 2` once `|z - w|` is small, uniformly in `a`; and `d_T (π z) (π w) ≤ d₁ z w`.
-/

namespace HSP

/-- The orbit map `π : Z⁺ → T` is uniformly continuous from the Euclidean distance to `d_T`. -/
theorem LocalDatum.π_uniformContinuous {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}
    (A : LocalDatum p n D ρplus) :
    ∀ ε > 0, ∃ δ > 0, ∀ z w : A.Zplus,
      dist ((z : A.Ω) : EuclideanSpace ℝ (Fin n)) ((w : A.Ω) : EuclideanSpace ℝ (Fin n)) < δ →
        A.dT (A.π z) (A.π w) < ε := by
  intro ε hε
  have : CompactSpace A.Zplus := isCompact_iff_compactSpace.1 A.isCompact_Zplus
  have huc : UniformContinuous fun q : ℤ_[p] × A.Zplus =>
      ((q.1 +ᵥ (q.2 : A.Ω) : A.Ω) : EuclideanSpace ℝ (Fin n)) :=
    CompactSpace.uniformContinuous_of_continuous (continuous_subtype_val.comp
      (continuous_fst.vadd (continuous_subtype_val.comp continuous_snd)))
  obtain ⟨δ, hδ, hδε⟩ := Metric.uniformContinuous_iff.1 huc (ε / 2) (half_pos hε)
  refine ⟨δ, hδ, fun z w hzw => ?_⟩
  have hd₁ : A.d₁ z w ≤ ε / 2 := ciSup_le fun a =>
    (hδε (a := (a, z)) (b := (a, w)) (by simpa [Prod.dist_eq, Subtype.dist_eq] using hzw)).le
  have hbdd : BddBelow (Set.range fun b : padicSubgroup p 1 => A.d₁ z ((b : ℤ_[p]) +ᵥ w)) :=
    ⟨0, by
      rintro _ ⟨b, rfl⟩
      exact Real.iSup_nonneg fun _ => dist_nonneg⟩
  have hle : A.dT (A.π z) (A.π w) ≤ A.d₁ z w := by
    have h := ciInf_le hbdd 0
    simp only [ZeroMemClass.coe_zero, zero_vadd] at h
    exact h
  linarith

end HSP
