import Mathlib
import HilbertSmithPaper.ChainModels.Torus.Lift
import HilbertSmithPaper.ChainModels.Grid.BufferedCells
import HilbertSmithPaper.ChainModels.Grid.SphereLabels
import HilbertSmithPaper.LocalData.Control.ControlSpace
import HilbertSmithPaper.LocalData.Chart.TestRegion
import HilbertSmithPaper.LocalData.Chart.OpenTestRegion
import HilbertSmithPaper.LocalData.Chart.TestMapProper
import HilbertSmithPaper.ChainModels.Approximations.TorusTestMap
import HilbertSmithPaper.Corner.Actions.GraphType

/-!
# Control labels

The control label of a buffered cell `b` (sphere label `s_b ∈ B(0, v)`) is
`λ(b) = (π(x̃_b), s_b) ∈ T × Sⁿ`, with `x̃_b ∈ [-2,2)ⁿ` the lift of the torus label and
`π : Z⁺ → T` the quotient onto the control space. Cells that are not buffered get no label.

## Encoding

* `lift_mem_Zplus` proves that `x̃_b` is (the image of) a point of the test region `Z⁺`: by
  definition `f(x̃_b) = f_T(x_b) = s_b ∈ B̄(0, v)`, so `x̃_b ∈ U⁺ ⊆ Z⁺` by preimages under the test
  map (which needs `0 < ρ < ρ₊`). `zplusPoint` is that point of `Z⁺`.
* `controlLabelOf` is the label of a torus point with buffered sphere label; `controlLabel`
  (the declaration of the article) labels buffered cells of `D_i`, `dualControlLabel` buffered
  dual cells. Both take the membership proof as an argument, so no base point of `T` is needed.
* `T × Sⁿ` is Mathlib's product, whose metric is the maximum of `d_T` and `d_S`.
-/

namespace HSP.ChainModels

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- If `f_T(x) ∈ B(0, v)`, the lift `x̃` is a point of the test region `Z⁺`. -/
lemma lift_mem_Zplus (A : LocalDatum p n D ρplus) {ρ : ℝ} (hρ : 0 < ρ) (hρ' : ρ < ρplus)
    {v : ℝ} {x : Torus n} (hx : IsBufferedLabel v (torusTestMap A ρ x : Corner.RoundSphere n)) :
    ∃ z : A.Zplus, ((z : A.Ω) : EuclideanSpace ℝ (Fin n)) = Torus.lift x := by
  have hC : IsCompact (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) v) :=
    isCompact_closedBall 0 v
  have hmem : (Torus.lift x : OnePoint (EuclideanSpace ℝ (Fin n))) ∈
      A.testMap ρ ⁻¹' ((↑) '' Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) v) := by
    obtain ⟨y, hy, hxy⟩ := hx
    exact ⟨y, Metric.ball_subset_closedBall hy, hxy⟩
  obtain ⟨w, ⟨u, hu, rfl⟩, hw⟩ := (A.isCompact_testMap_preimage hρ hρ' hC).2 hmem
  exact ⟨⟨u, show ‖A.F₀ u‖ ≤ ρplus from le_of_lt hu⟩, OnePoint.coe_injective hw⟩

/-- The point `x̃ ∈ Z⁺` of a torus point with buffered sphere label. -/
noncomputable def zplusPoint (A : LocalDatum p n D ρplus) {ρ : ℝ} (hρ : 0 < ρ) (hρ' : ρ < ρplus)
    {v : ℝ} {x : Torus n} (hx : IsBufferedLabel v (torusTestMap A ρ x : Corner.RoundSphere n)) :
    A.Zplus :=
  (lift_mem_Zplus A hρ hρ' hx).choose

/-- The control label `(π(x̃), f_T(x)) ∈ T × Sⁿ` of a torus point with buffered sphere label. -/
noncomputable def controlLabelOf (A : LocalDatum p n D ρplus) {ρ : ℝ} (hρ : 0 < ρ)
    (hρ' : ρ < ρplus) {v : ℝ} (x : Torus n)
    (hx : IsBufferedLabel v (torusTestMap A ρ x : Corner.RoundSphere n)) :
    A.T × Corner.RoundSphere n :=
  (A.π (zplusPoint A hρ hρ' hx), torusTestMap A ρ x)

/-- The *control label* `λ(b) = (π(x̃_b), s_b)` of a buffered basis cell `b = a` of `(D_i)_r`. -/
noncomputable def controlLabel (A : LocalDatum p n D ρplus) {ρ : ℝ} (hρ : 0 < ρ)
    (hρ' : ρ < ρplus) (i : ℕ) (r : ℤ) (v : ℝ) (a : bufferedCells A ρ i r v) :
    A.T × Corner.RoundSphere n :=
  controlLabelOf A hρ hρ' (chainModelLabel A i r a) a.2

/-- The control label of a buffered dual cell `a^*` of `(D_i^{N-*})_r`. -/
noncomputable def dualControlLabel (A : LocalDatum p n D ρplus) {ρ : ℝ} (hρ : 0 < ρ)
    (hρ' : ρ < ρplus) (i : ℕ) (r : ℤ) (v : ℝ) (a : bufferedDualCells A ρ i r v) :
    A.T × Corner.RoundSphere n :=
  controlLabelOf A hρ hρ' (chainModelDualLabel A i r a) a.2

end HSP.ChainModels
