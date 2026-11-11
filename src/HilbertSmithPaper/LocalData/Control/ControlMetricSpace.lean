import Mathlib
import HilbertSmithPaper.LocalData.Control.ControlMetricProperties

/-!
# The metric on the control space

The control space `T` carries the orbit metric `d_T`; its topology is the quotient topology.

## Encoding

`HSP.LocalDatum.instMetricSpaceT` (the declaration of the article) is built with
`MetricSpace.ofDistTopology`, so its topology is (definitionally) the quotient topology.
-/

namespace HSP

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- The metric space structure on the control space given by `d_T`; its topology is the quotient
topology. -/
noncomputable instance LocalDatum.instMetricSpaceT (A : LocalDatum p n D ρplus) :
    MetricSpace A.T :=
  MetricSpace.ofDistTopology A.dT A.dT_metric.1 A.dT_metric.2.1 A.dT_metric.2.2.1
    A.dT_metric.2.2.2.2 A.dT_metric.2.2.2.1

end HSP
