import Mathlib
import HilbertSmithPaper.Compression.BufferConditions
import HilbertSmithPaper.ChainModels.Grid.ChainModelEstimates

/-!
# Buffers hold eventually

For fixed local data there are `i₁` and a null sequence `(ε'_i)` of nonnegative reals such that
the buffer conditions
hold with `(ε'_i)` for every `i ≥ i₁`.

## Encoding

`buffer_eventually` (the declaration of the article) asserts a nonnegative null sequence `ε'` with
`BuffersHold F ε' i` for all large `i` (`∀ᶠ i in atTop`, which is "there is `i₁` such that for
every `i ≥ i₁`"). The sequence `ε'` is `max ε_v 0` for the sequence `ε_v` of chain-model
estimates (4) at `v = u` (a larger bound preserves graph type); item (1) uses that the center of a
cube (the torus label) lies in its closed cube.
-/

open Filter Topology

namespace HSP.Compression

open HSP.ChainModels

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- The center of a cube lies in its closed cube. -/
private lemma center_mem_realization {k : ℕ} (hk : 0 < k) (c : GridCube k n) :
    c.center ∈ c.realization := by
  intro j _
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  simp only [GridCube.center, cellRealization]
  rcases hb : (c j).2
  · simp
  · simp only [ite_true]
    refine ⟨(4 * ((c j).1 : ℕ) + 2) / k, ⟨?_, ?_⟩, rfl⟩
    · exact div_le_div_of_nonneg_right (by linarith) hk'.le
    · exact div_le_div_of_nonneg_right (by linarith) hk'.le

/-- Item (1) at one index, for a cell of `(D_i)_r`. -/
private lemma retained_buffered (F : FixedLocalData p n D ρplus) {i : ℕ} {δ e : ℝ}
    (hδ : Metric.thickening δ ((↑) '' Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) F.t) ⊆
      ((↑) '' Metric.ball (0 : EuclideanSpace ℝ (Fin n)) ((F.t + F.u) / 2) :
        Set (Corner.RoundSphere n)))
    (hdiam : ∀ c : GridCube (meshSequence F.toLocalDatum i) n,
      Metric.diam ((fun y => (torusTestMap F.toLocalDatum F.ρ y : Corner.RoundSphere n)) ''
        c.realization) ≤ e)
    (he : e < δ) (r : ℤ) (a : Fin ((chainModel F.toLocalDatum i).X r).dim)
    (ha : IsRetained F i r a) :
    a ∈ bufferedCells F.toLocalDatum F.ρ (chainModelLabel F.toLocalDatum i r) ((F.t + F.u) / 2) := by
  obtain ⟨y, hyc, hyK⟩ := ha
  set c := chainModelCube F.toLocalDatum i r a
  have hk : 0 < meshSequence F.toLocalDatum i :=
    lt_of_lt_of_le (by norm_num) (eight_le_meshSequence F.toLocalDatum i)
  have hx : c.center ∈ c.realization := center_mem_realization hk c
  have hd : dist (torusTestMap F.toLocalDatum F.ρ c.center : Corner.RoundSphere n)
      (torusTestMap F.toLocalDatum F.ρ y) ≤ e :=
    (Metric.dist_le_diam_of_mem (isCompact_univ.isBounded.subset (Set.subset_univ _))
      (Set.mem_image_of_mem
        (fun y => (torusTestMap F.toLocalDatum F.ρ y : Corner.RoundSphere n)) hx)
      (Set.mem_image_of_mem
        (fun y => (torusTestMap F.toLocalDatum F.ρ y : Corner.RoundSphere n)) hyc)).trans
      (hdiam c)
  apply hδ
  exact Metric.mem_thickening_iff.2 ⟨_, hyK, lt_of_le_of_lt hd he⟩

/-- **Buffers hold eventually.** There are an index `i₁` and a null sequence `(ε'_i)` of
nonnegative reals such that
the buffer conditions hold with `(ε'_i)` for every `i ≥ i₁`. -/
theorem buffer_eventually (F : FixedLocalData p n D ρplus) :
    ∃ ε' : ℕ → ℝ, Tendsto ε' atTop (𝓝 0) ∧ (∀ i, 0 ≤ ε' i) ∧
      ∀ᶠ i in atTop, BuffersHold F ε' i := by
  have ht : 0 < F.t := F.r_pos.trans (F.r_lt_R.trans F.R_lt_t)
  have htu : F.t < F.u := F.t_lt_u
  obtain ⟨ε, hε, -, -, h3, h4, h5⟩ := chainModel_estimates F.toLocalDatum F.ρ_pos F.ρ_lt
  obtain ⟨i₀, εv, hεv, h4'⟩ := h4 F.u (ht.trans htu)
  obtain ⟨i₁, h5'⟩ := h5 ((F.t + F.u) / 2) F.u (by linarith) (by linarith)
  -- the separation of `B̄(0,t)` from the complement of `B(0,t')`
  set K : Set (Corner.RoundSphere n) :=
    (↑) '' Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) F.t
  set U : Set (Corner.RoundSphere n) :=
    (↑) '' Metric.ball (0 : EuclideanSpace ℝ (Fin n)) ((F.t + F.u) / 2)
  have hK : IsCompact K :=
    (isCompact_closedBall _ _).image OnePoint.continuous_coe
  have hU : IsOpen U := OnePoint.isOpenEmbedding_coe.isOpenMap _ Metric.isOpen_ball
  have hKU : K ⊆ U := Set.image_mono (Metric.closedBall_subset_ball (by linarith))
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_thickening_subset_open hU hKU
  have hev : ∀ᶠ i in atTop, ε i < δ := hε.eventually (gt_mem_nhds hδ)
  refine ⟨fun i => max (εv i) 0, by simpa using hεv.max (tendsto_const_nhds (x := (0 : ℝ))),
    fun i => le_max_right _ _, ?_⟩
  filter_upwards [hev, eventually_ge_atTop i₀, eventually_ge_atTop i₁] with i hi hi₀ hi₁
  refine ⟨⟨fun r a ha => retained_buffered F hδU (h3 i) hi r a ha,
    fun r a ha => retained_buffered F hδU (h3 i) hi _ a ha⟩, h5' i hi₁,
    fun w hw b' b h => (h4' i hi₀ w hw b' b h).trans (le_max_left _ _)⟩

end HSP.Compression
