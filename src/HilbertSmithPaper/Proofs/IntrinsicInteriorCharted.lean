import HilbertSmithPaper.Proofs.IntrinsicInterior
import HilbertSmithPaper.Proofs.IntrinsicInteriorOpen

/-!
# The intrinsic interior is charted

The subspace `M°ₙ` carries an atlas modelled on `ℝⁿ`: at each point `x` choose a homeomorphism
`e` from an open subset of `M` containing `x` onto an open subset of `ℝⁿ`; since `M°ₙ` is open,
`e` restricts to a chart of the subspace (`OpenPartialHomeomorph.subtypeRestr`), whose domain is
the part of the domain of `e` in `M°ₙ`, namely all of it. The atlas is the set of these chosen
charts.
-/

namespace HSP

/-- The chosen homeomorphism at a point `x` of `M°ₙ`, from an open subset of `M` containing `x`
onto an open subset of `ℝⁿ`. -/
private noncomputable def chosenChart {n : ℕ} {M : Type*} [TopologicalSpace M]
    (x : intrinsicInterior n M) : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)) :=
  Classical.choose x.2

/-- The atlas on the intrinsic interior: the chart at `x` is the chosen homeomorphism at `x`
restricted to the open subspace `M°ₙ`. -/
noncomputable instance intrinsicInterior.chartedSpace (n : ℕ) (M : Type*) [TopologicalSpace M] :
    ChartedSpace (EuclideanSpace ℝ (Fin n)) (intrinsicInterior n M) where
  atlas := Set.range fun x : intrinsicInterior n M =>
    (chosenChart x).subtypeRestr (s := ⟨_, isOpen_intrinsicInterior n M⟩) ⟨x⟩
  chartAt x := (chosenChart x).subtypeRestr (s := ⟨_, isOpen_intrinsicInterior n M⟩) ⟨x⟩
  mem_chart_source x := by
    rw [OpenPartialHomeomorph.subtypeRestr_source]
    exact Classical.choose_spec x.2
  chart_mem_atlas x := Set.mem_range_self x

end HSP
