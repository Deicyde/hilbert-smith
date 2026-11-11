import HilbertSmithPaper.Inputs.CompactGroups.ZpInTorsionFree
import HilbertSmithPaper.Inputs.GleasonYamabe.GleasonYamabe
import HilbertSmithPaper.Inputs.Newman.NewmanOpenSet
import HilbertSmithPaper.Inputs.Newman.NewmanSmallOrbits
import HilbertSmithPaper.LTheory.Base.Categories.DualityCategory
import HilbertSmithPaper.Proofs.FaithfulHausdorff
import HilbertSmithPaper.Proofs.HilbertSmith
import HilbertSmithPaper.Proofs.IntegerTails
import HilbertSmithPaper.Proofs.InteriorAction
import HilbertSmithPaper.Proofs.InteriorActionContinuous
import HilbertSmithPaper.Proofs.InteriorActionFaithful
import HilbertSmithPaper.Proofs.IntrinsicInterior
import HilbertSmithPaper.Proofs.IntrinsicInteriorCharted
import HilbertSmithPaper.Proofs.IntrinsicInteriorConnected
import HilbertSmithPaper.Proofs.IntrinsicInteriorDense
import HilbertSmithPaper.Proofs.IntrinsicInteriorInvariant
import HilbertSmithPaper.Proofs.IntrinsicInteriorOpen
import HilbertSmithPaper.Proofs.LocalExclusion
import HilbertSmithPaper.Proofs.NoSmallSubgroups
import HilbertSmithPaper.Proofs.OneChart
import HilbertSmithPaper.Proofs.PadicExclusion
import HilbertSmithPaper.Proofs.PadicExclusionBoundary

/-!
# The paper

The Lean side of the paper in `blueprint/roadmap/paper/`: every formalizable article there names
one declaration of this library in its `lean:` field, and states exactly what that declaration
states. Declarations live in the namespace `HSP`.

This library imports only Mathlib and TauCeti.
-/
