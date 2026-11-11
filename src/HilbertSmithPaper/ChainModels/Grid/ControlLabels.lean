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

* A private lemma proves that `x̃_b` is (the image of) a point of the test region `Z⁺`: by
  definition `f(x̃_b) = f_T(x_b) ∈ B̄(0, v)`, so `x̃_b ∈ U⁺ ⊆ Z⁺` by preimages under the test map
  (which needs `0 < ρ < ρ₊`).
* `controlLabel A hρ hρ' x v b` (the declaration of the article) labels the buffered cells of any
  set of cells with torus labels `x` (`bufferedCells`); for `D_i` in degree `r`, `x` is
  `chainModelLabel A i r`, for the dual cells `chainModelDualLabel A i r`. It takes the membership
  proof as an argument, so no base point of `T` is needed.
* `T × Sⁿ` is Mathlib's product, whose metric is the maximum of `d_T` and `d_S`.
-/

namespace HSP.ChainModels

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- If `f_T(x) ∈ B(0, v)`, the lift `x̃` is a point of the test region `Z⁺`. -/
private lemma lift_mem_Zplus (A : LocalDatum p n D ρplus) {ρ : ℝ} (hρ : 0 < ρ) (hρ' : ρ < ρplus)
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
private noncomputable def zplusPoint (A : LocalDatum p n D ρplus) {ρ : ℝ} (hρ : 0 < ρ)
    (hρ' : ρ < ρplus)
    {v : ℝ} {x : Torus n} (hx : IsBufferedLabel v (torusTestMap A ρ x : Corner.RoundSphere n)) :
    A.Zplus :=
  (lift_mem_Zplus A hρ hρ' hx).choose

/-- The *control label* `λ(b) = (π(x̃_b), f_T(x_b)) ∈ T × Sⁿ` of a buffered cell `b ∈ 𝓑(v)` of a
set of cells with torus labels `x`; for the cells of `D_i` and their duals, `f_T(x_b) = s_b`. -/
noncomputable def controlLabel (A : LocalDatum p n D ρplus) {ρ : ℝ} (hρ : 0 < ρ)
    (hρ' : ρ < ρplus) {B : Type*} (x : B → Torus n) (v : ℝ) (b : bufferedCells A ρ x v) :
    A.T × Corner.RoundSphere n :=
  (A.π (zplusPoint A hρ hρ' b.2), torusTestMap A ρ (x b))

end HSP.ChainModels
