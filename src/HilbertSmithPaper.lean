import HilbertSmithPaper.Inputs.CompactGroups.ZpInTorsionFree
import HilbertSmithPaper.Inputs.GleasonYamabe.GleasonYamabe
import HilbertSmithPaper.Inputs.Newman.NewmanOpenSet
import HilbertSmithPaper.Inputs.Newman.NewmanSmallOrbits
import HilbertSmithPaper.LTheory.Base.Categories.DualityCategory
import HilbertSmithPaper.Proofs.FaithfulHausdorff
import HilbertSmithPaper.Proofs.IntegerTails
import HilbertSmithPaper.Proofs.PadicExclusion

/-!
# The paper

The Lean side of the paper in `blueprint/roadmap/paper/`: every formalizable article there names
one declaration of this library in its `lean:` field, and states exactly what that declaration
states. Declarations live in the namespace `HSP`.

This library imports only Mathlib and TauCeti.
-/
