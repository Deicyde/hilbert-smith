import HilbertSmithPaper.LTheory.Base.Categories.DualityCategory
import HilbertSmithPaper.LocalData.Chart.LocalDatum
import HilbertSmithPaper.LocalData.Chart.Pinch
import HilbertSmithPaper.LocalData.Chart.PinchContinuous
import HilbertSmithPaper.LocalData.Control.FixedLocalData
import HilbertSmithPaper.LocalData.Control.ReductionKernel
import HilbertSmithPaper.LocalData.Control.RepresentativeMap
import HilbertSmithPaper.LocalData.Subgroups.ClosedSubgroups
import HilbertSmithPaper.LocalData.Subgroups.FixedSets
import HilbertSmithPaper.LocalData.Subgroups.PadicSubgroups
import HilbertSmithPaper.LocalData.Subgroups.PadicSubgroupsBasis
import HilbertSmithPaper.LocalData.Subgroups.SmallDisplacement

/-!
# The paper

The Lean side of the paper in `blueprint/roadmap/paper/`: every formalizable article there names
one declaration of this library in its `lean:` field, and states exactly what that declaration
states. Declarations live in the namespace `HSP`.

This library imports only Mathlib and TauCeti.
-/
