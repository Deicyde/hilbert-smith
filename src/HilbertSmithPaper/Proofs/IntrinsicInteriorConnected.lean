import HilbertSmithPaper.Proofs.IntrinsicInterior
import HilbertSmithPaper.Proofs.HalfSpaceInterior
import HilbertSmithPaper.Proofs.OpenHalfSpaceDense
import HilbertSmithPaper.Proofs.IntrinsicInteriorDense

/-!
# The intrinsic interior is connected

`M°ₙ` is nonempty since it is dense. Each point `x` of `M` has a neighbourhood `V` (the part of
the chart domain mapped into a ball around `φ x`) such that `V ∩ M°ₙ` is preconnected: it contains
the part `V⁺` over the open half-ball, which is the image of a convex set under `φ⁻¹`, and lies in
the closure of `V⁺`. Given a separation of `M°ₙ` by open sets `u, v`, the points having such a
neighbourhood whose trace on `M°ₙ` lies in `u` (resp. `v`) form two open sets covering `M`; they
are disjoint by density, and nonempty, contradicting the connectedness of `M`.
-/

open scoped Manifold Topology

namespace HSP

/-- Every point has a neighbourhood whose trace on the intrinsic interior is preconnected. -/
private theorem exists_nhds_isPreconnected_inter {n : ℕ} [NeZero n] {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace n) M] (x : M) :
    ∃ V ∈ 𝓝 x, IsPreconnected (V ∩ intrinsicInterior n M) := by
  set φ := chartAt (EuclideanHalfSpace n) x
  have hx : x ∈ φ.source := mem_chart_source _ x
  obtain ⟨T, hT, hTeq⟩ := isOpen_induced_iff.1 φ.open_target
  have hxT : (φ x).1 ∈ T := by
    have : φ x ∈ φ.target := φ.map_source hx
    rw [← hTeq] at this
    exact this
  obtain ⟨r, hr, hrT⟩ := Metric.isOpen_iff.1 hT _ hxT
  -- the relative half-ball `B` around `φ x`, inside the target of `φ`
  set B : Set (EuclideanHalfSpace n) := Subtype.val ⁻¹' Metric.ball (φ x).1 r
  set U : Set (EuclideanHalfSpace n) := {z | 0 < z.1 0}
  have hBt : B ⊆ φ.target := fun z hz => by rw [← hTeq]; exact hrT hz
  have hBo : IsOpen B := Metric.isOpen_ball.preimage continuous_subtype_val
  refine ⟨φ.source ∩ φ ⁻¹' B, (φ.isOpen_inter_preimage hBo).mem_nhds
    ⟨hx, Metric.mem_ball_self hr⟩, ?_⟩
  have hcont : ContinuousOn φ.symm B := φ.continuousOn_symm.mono hBt
  have hpre : IsPreconnected (φ.symm '' (B ∩ U)) := by
    refine IsPreconnected.image ?_ _ (hcont.mono Set.inter_subset_left)
    have hind : Topology.IsInducing
        (Subtype.val : EuclideanHalfSpace n → EuclideanSpace ℝ (Fin n)) :=
      Topology.IsInducing.subtypeVal
    rw [← hind.isPreconnected_image]
    have himg : Subtype.val '' (B ∩ U) =
        Metric.ball (φ x).1 r ∩ {y : EuclideanSpace ℝ (Fin n) | 0 < y 0} := by
      ext y
      constructor
      · rintro ⟨z, ⟨hzB, hzU⟩, rfl⟩
        exact ⟨hzB, hzU⟩
      · rintro ⟨hyB, hyU⟩
        exact ⟨⟨y, le_of_lt hyU⟩, ⟨hyB, hyU⟩, rfl⟩
    rw [himg]
    have hlin : IsLinearMap ℝ fun y : EuclideanSpace ℝ (Fin n) => y 0 :=
      { map_add := fun _ _ => by simp
        map_smul := fun _ _ => by simp }
    exact ((convex_ball _ _).inter (convex_halfSpace_gt hlin 0)).isPreconnected
  refine hpre.subset_closure ?_ ?_
  · rintro _ ⟨z, hz, rfl⟩
    have hzt := hBt hz.1
    refine ⟨⟨φ.map_target hzt, ?_⟩, mem_intrinsicInterior_of_pos φ (φ.map_target hzt) ?_⟩
    · show φ (φ.symm z) ∈ B
      rw [φ.right_inv hzt]
      exact hz.1
    · rw [φ.right_inv hzt]
      exact hz.2
  · rintro y ⟨⟨hys, hyB⟩, -⟩
    have h1 : φ y ∈ closure (B ∩ U) :=
      hBo.inter_closure ⟨hyB, dense_pos_halfSpace (φ y)⟩
    have h2 := ((φ.continuousOn_symm (φ y) (φ.map_source hys)).mono
      fun z hz => hBt hz.1).mem_closure_image h1
    rwa [φ.left_inv hys] at h2

/-- For `n ≥ 1` and a connected space `M` with an atlas on the half-space
`{x ∈ ℝⁿ | x 0 ≥ 0}`, the intrinsic interior `M°ₙ` is connected. -/
theorem isConnected_intrinsicInterior {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
    [ConnectedSpace M] [ChartedSpace (EuclideanHalfSpace n) M] :
    IsConnected (intrinsicInterior n M) := by
  set S := intrinsicInterior n M
  have hdense : Dense S := dense_intrinsicInterior
  refine ⟨hdense.nonempty, fun u v hu hv hSuv hSu hSv => ?_⟩
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  -- the points with a neighbourhood whose trace on `S` lies in `u`, resp. `v`
  set A : Set M := {x | ∃ V ∈ 𝓝 x, V ∩ S ⊆ u}
  set B : Set M := {x | ∃ V ∈ 𝓝 x, V ∩ S ⊆ v}
  have hopen : ∀ w : Set M, IsOpen {x | ∃ V ∈ 𝓝 x, V ∩ S ⊆ w} := fun w =>
    isOpen_iff_mem_nhds.2 fun x ⟨V, hV, hVw⟩ =>
      Filter.mem_of_superset (eventually_eventually_nhds.2 hV) fun y hy => ⟨V, hy, hVw⟩
  have hcover : Set.univ ⊆ A ∪ B := by
    intro x _
    obtain ⟨V, hV, hVc⟩ := exists_nhds_isPreconnected_inter (n := n) x
    have h0 : V ∩ S ∩ (u ∩ v) = ∅ :=
      Set.subset_empty_iff.1 (hne ▸ fun y hy => ⟨hy.1.2, hy.2⟩)
    rcases isPreconnected_iff_subset_of_disjoint.1 hVc u v hu hv
        (fun y hy => hSuv hy.2) h0 with h | h
    · exact Or.inl ⟨V, hV, h⟩
    · exact Or.inr ⟨V, hV, h⟩
  obtain ⟨x, -, hxA, hxB⟩ := PreconnectedSpace.isPreconnected_univ A B (hopen u) (hopen v)
    hcover (by
      obtain ⟨y, hyS, hyu⟩ := hSu
      exact ⟨y, trivial, u, hu.mem_nhds hyu, fun z hz => hz.1⟩)
    (by
      obtain ⟨y, hyS, hyv⟩ := hSv
      exact ⟨y, trivial, v, hv.mem_nhds hyv, fun z hz => hz.1⟩)
  obtain ⟨V₁, hV₁, h₁⟩ := hxA
  obtain ⟨V₂, hV₂, h₂⟩ := hxB
  obtain ⟨y, hy₁₂, hyS⟩ := mem_closure_iff_nhds.1 (hdense x) _ (Filter.inter_mem hV₁ hV₂)
  have : y ∈ S ∩ (u ∩ v) := ⟨hyS, h₁ ⟨hy₁₂.1, hyS⟩, h₂ ⟨hy₁₂.2, hyS⟩⟩
  rw [hne] at this
  exact this

end HSP
