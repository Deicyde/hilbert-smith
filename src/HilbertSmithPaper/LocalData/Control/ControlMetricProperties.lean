import Mathlib
import HilbertSmithPaper.LocalData.Control.ControlMetric

/-!
# The orbit metric metrizes the control space

`d_T` is a metric on `T` (`d_T s s = 0`, symmetry, the triangle inequality, `d_T s t = 0 → s = t`)
whose open sets are exactly the open sets of the quotient topology: `U` is open iff every `s ∈ U`
has some `ε > 0` with `{t | d_T s t < ε} ⊆ U`.

## Companion

`HSP.LocalDatum.instMetricSpaceT` is the resulting `MetricSpace` structure on `T`, built with
`MetricSpace.ofDistTopology`, so its topology is (definitionally) the quotient topology.
-/

namespace HSP

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- `d_T` is a metric on the control space inducing its quotient topology. -/
theorem LocalDatum.dT_metric (A : LocalDatum p n D ρplus) :
    (∀ s, A.dT s s = 0) ∧ (∀ s t, A.dT s t = A.dT t s) ∧
      (∀ s t u, A.dT s u ≤ A.dT s t + A.dT t u) ∧ (∀ s t, A.dT s t = 0 → s = t) ∧
      ∀ U : Set A.T, IsOpen U ↔ ∀ s ∈ U, ∃ ε > 0, ∀ t, A.dT s t < ε → t ∈ U := by
  sorry

/-- The metric space structure on the control space given by `d_T`; its topology is the quotient
topology. -/
noncomputable instance LocalDatum.instMetricSpaceT (A : LocalDatum p n D ρplus) :
    MetricSpace A.T :=
  MetricSpace.ofDistTopology A.dT A.dT_metric.1 A.dT_metric.2.1 A.dT_metric.2.2.1
    A.dT_metric.2.2.2.2 A.dT_metric.2.2.2.1

end HSP
