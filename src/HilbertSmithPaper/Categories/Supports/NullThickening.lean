import HilbertSmithPaper.Categories.Asymptotic.AsymptoticCategory

/-!
# Null thickening radii

If for every `ε > 0` the labels `x_i(k)` with `Q i k` eventually lie in the `ε`-thickening of `S'`,
then some null sequence `r` has these labels eventually in the closed `r_i`-thickenings of `S'`
(take `r_i` the largest `infEDist` to `S'`, which is eventually finite).
-/

open Filter Topology Metric
open scoped NNReal ENNReal

namespace HSP

variable {p : ℕ} {G : GroupSeq p} {X : Type*} [MetricSpace X] [AddAction (ZMod p) X]

omit [AddAction (ZMod p) X] in
/-- A null sequence bounding, eventually, the closed thickenings of `S'` containing the `x_i(k)`
with `Q i k`, provided that for every `ε > 0` these points are eventually `ε`-close to `S'`. -/
theorem exists_null_cthickening {M : AsymPre G X} (S' : Set X) (Q : ∀ i, Fin (M.n i) → Prop)
    (h : ∀ ε > 0, ∀ᶠ i in atTop, ∀ k, Q i k → M.x i k ∈ thickening ε S') :
    ∃ r : ℕ → ℝ≥0, Tendsto r atTop (𝓝 0) ∧
      ∀ᶠ i in atTop, ∀ k, Q i k → M.x i k ∈ cthickening (r i) S' := by
  classical
  let f : ℕ → ℝ≥0∞ := fun i =>
    Finset.univ.sup fun k => if Q i k then Metric.infEDist (M.x i k) S' else 0
  have hf : Tendsto f atTop (𝓝 0) := by
    rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    obtain ⟨δ, hδ0, hδε⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hε
    filter_upwards [h δ (NNReal.coe_pos.2 (ENNReal.coe_pos.1 hδ0))] with i hi
    refine Finset.sup_le fun k _ => ?_
    split_ifs with hk
    · have := mem_thickening_iff_infEDist_lt.1 (hi k hk)
      rw [ENNReal.ofReal_coe_nnreal] at this
      exact (this.trans hδε).le
    · exact zero_le
  refine ⟨fun i => (f i).toNNReal, ?_, ?_⟩
  · have := (ENNReal.tendsto_toNNReal ENNReal.zero_ne_top).comp hf
    simpa [Function.comp_def] using this
  · filter_upwards [hf.eventually (gt_mem_nhds zero_lt_one)] with i hi k hk
    rw [mem_cthickening_iff, ENNReal.ofReal_coe_nnreal,
      ENNReal.coe_toNNReal (hi.trans ENNReal.one_lt_top).ne]
    refine le_trans (le_of_eq ?_) (Finset.le_sup (f := fun k =>
      if Q i k then Metric.infEDist (M.x i k) S' else 0) (Finset.mem_univ k))
    simp only [hk, ↓reduceIte]


end HSP
