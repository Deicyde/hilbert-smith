import HilbertSmithPaper.LTheory.Base.Categories.DualityCategory
import HilbertSmithPaper.Categories.Asymptotic.GroupSequence
import HilbertSmithPaper.Categories.Asymptotic.Propagation
import HilbertSmithPaper.Categories.Asymptotic.PropAdd
import HilbertSmithPaper.Categories.Asymptotic.PropMul
import HilbertSmithPaper.Categories.Asymptotic.PropRelabel
import HilbertSmithPaper.Categories.Asymptotic.PropSmul
import HilbertSmithPaper.Categories.Asymptotic.PropTranspose

/-!
# The paper

The Lean side of the paper in `blueprint/roadmap/paper/`: every formalizable article there names
one declaration of this library in its `lean:` field, and states exactly what that declaration
states. Declarations live in the namespace `HSP`.

This library imports only Mathlib and TauCeti.
-/
