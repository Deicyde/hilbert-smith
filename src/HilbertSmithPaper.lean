import HilbertSmithPaper.LTheory.Base.Categories.DualityCategory
import HilbertSmithPaper.LTheory.Base.Categories.DualityFunctor
import HilbertSmithPaper.LTheory.Base.Categories.KaroubiDuality
import HilbertSmithPaper.LTheory.Base.Categories.KaroubiEmbedding
import HilbertSmithPaper.LTheory.Base.Categories.KaroubiFunctor
import HilbertSmithPaper.LocalData.Chart.AveragedMap
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
import HilbertSmithPaper.Categories.Asymptotic.GroupSequence
import HilbertSmithPaper.Categories.Asymptotic.Propagation
import HilbertSmithPaper.Categories.Asymptotic.PropAdd
import HilbertSmithPaper.Categories.Asymptotic.PropMul
import HilbertSmithPaper.Categories.Asymptotic.PropRelabel
import HilbertSmithPaper.Categories.Asymptotic.PropSmul
import HilbertSmithPaper.Categories.Asymptotic.PropTranspose
import HilbertSmithPaper.Signatures.Forms.FormSignature
import HilbertSmithPaper.Signatures.Forms.FormSignatureIsometry
import HilbertSmithPaper.Signatures.Forms.FormSignatureNeg
import HilbertSmithPaper.Signatures.LFour.SignatureSplittingExists
import HilbertSmithPaper.Signatures.LFour.SignatureSplittingIndependence

/-!
# The paper

The Lean side of the paper in `blueprint/roadmap/paper/`: every formalizable article there names
one declaration of this library in its `lean:` field, and states exactly what that declaration
states. Declarations live in the namespace `HSP`.

This library imports only Mathlib and TauCeti.
-/
