import Mathlib
import HilbertSmithPaper.LocalData.Control.OrbitSupMetric

/-!
# The orbit sup-distance is a metric

`d₁` is a metric on `Z⁺` (`d₁ z z = 0`, symmetry, the triangle inequality, `d₁ z w = 0 → z = w`)
whose open sets are those of the subspace topology of `Z⁺ ⊆ ℝⁿ`: `U` is open iff every `z ∈ U` has
some `ε > 0` with `{w | d₁ z w < ε} ⊆ U`.

The metric axioms hold for each `a` and pass to the supremum (bounded, as a continuous function on
the compact `ℤ_[p]`). Since `|z - w| ≤ d₁ z w` (the term `a = 0`), Euclidean-open sets are
`d₁`-open. Conversely, the tube lemma for the compact `ℤ_[p]` and the jointly continuous
`(a, w) ↦ |a +ᵥ z - a +ᵥ w|` makes `{w | d₁ z w < ε}` a Euclidean neighbourhood of `z`.
-/

open Topology

namespace HSP

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

private lemma bddAbove_orbit_dist (A : LocalDatum p n D ρplus) (z w : A.Zplus) :
    BddAbove (Set.range fun a : ℤ_[p] =>
      dist ((a +ᵥ (z : A.Ω) : A.Ω) : EuclideanSpace ℝ (Fin n)) (a +ᵥ (w : A.Ω) : A.Ω)) := by
  refine (isCompact_range ?_).bddAbove
  exact (continuous_subtype_val.comp (continuous_id.vadd continuous_const)).dist
    (continuous_subtype_val.comp (continuous_id.vadd continuous_const))

private lemma dist_le_d₁ (A : LocalDatum p n D ρplus) (z w : A.Zplus) :
    dist ((z : A.Ω) : EuclideanSpace ℝ (Fin n)) (w : A.Ω) ≤ A.d₁ z w := by
  have := le_ciSup (bddAbove_orbit_dist A z w) 0
  simp only [zero_vadd] at this
  exact this

/-- `d₁` is a metric on `Z⁺` inducing its subspace topology. -/
theorem LocalDatum.d₁_metric (A : LocalDatum p n D ρplus) :
    (∀ z, A.d₁ z z = 0) ∧ (∀ z w, A.d₁ z w = A.d₁ w z) ∧
      (∀ z w u, A.d₁ z u ≤ A.d₁ z w + A.d₁ w u) ∧ (∀ z w, A.d₁ z w = 0 → z = w) ∧
      ∀ U : Set A.Zplus, IsOpen U ↔ ∀ z ∈ U, ∃ ε > 0, ∀ w, A.d₁ z w < ε → w ∈ U := by
  refine ⟨fun z => by simp [LocalDatum.d₁], fun z w => by simp [LocalDatum.d₁, dist_comm],
    fun z w u => ?_, fun z w h => ?_, fun U => ⟨fun hU z hz => ?_, fun hU => ?_⟩⟩
  · refine ciSup_le fun a => (dist_triangle _
      ((a +ᵥ (w : A.Ω) : A.Ω) : EuclideanSpace ℝ (Fin n)) _).trans (add_le_add ?_ ?_)
    · exact le_ciSup (bddAbove_orbit_dist A z w) a
    · exact le_ciSup (bddAbove_orbit_dist A w u) a
  · have h0 := dist_le_d₁ A z w
    rw [h] at h0
    exact Subtype.ext (Subtype.ext (dist_le_zero.1 h0))
  · obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU z hz
    refine ⟨ε, hε, fun w hw => hball ?_⟩
    rw [Metric.mem_ball, dist_comm]
    exact (dist_le_d₁ A z w).trans_lt hw
  · rw [isOpen_iff_mem_nhds]
    intro z hz
    obtain ⟨ε, hε, hεU⟩ := hU z hz
    set N : Set (ℤ_[p] × A.Zplus) := {q | dist ((q.1 +ᵥ (z : A.Ω) : A.Ω) :
      EuclideanSpace ℝ (Fin n)) (q.1 +ᵥ (q.2 : A.Ω) : A.Ω) < ε / 2}
    have hN : IsOpen N := isOpen_lt
      ((continuous_subtype_val.comp (continuous_fst.vadd continuous_const)).dist
        (continuous_subtype_val.comp (continuous_fst.vadd
          (continuous_subtype_val.comp continuous_snd)))) continuous_const
    have hsub : (Set.univ : Set ℤ_[p]) ×ˢ ({z} : Set A.Zplus) ⊆ N := by
      rintro ⟨a, w⟩ ⟨-, hw⟩
      simp only [Set.mem_singleton_iff] at hw
      subst hw
      simpa [N] using half_pos hε
    obtain ⟨u, v, -, hv, hu, hzv, huv⟩ :=
      generalized_tube_lemma isCompact_univ isCompact_singleton hN hsub
    refine Filter.mem_of_superset (hv.mem_nhds (hzv rfl)) fun w hw => hεU w ?_
    refine lt_of_le_of_lt (ciSup_le fun a => ?_) (half_lt_self hε)
    exact (huv (Set.mk_mem_prod (hu (Set.mem_univ a)) hw)).le

end HSP
