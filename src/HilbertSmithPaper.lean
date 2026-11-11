import HilbertSmithPaper.LTheory.Base.Categories.DualityCategory
import HilbertSmithPaper.LTheory.Base.Categories.DualityFunctor
import HilbertSmithPaper.LTheory.Base.Categories.KaroubiDuality
import HilbertSmithPaper.LTheory.Base.Categories.KaroubiEmbedding
import HilbertSmithPaper.LTheory.Base.Categories.KaroubiFunctor
import HilbertSmithPaper.LTheory.Base.Complexes.Cone
import HilbertSmithPaper.LTheory.Base.Complexes.DualComplex
import HilbertSmithPaper.LTheory.Base.Complexes.StructureComplex
import HilbertSmithPaper.LTheory.Base.Complexes.CycleChainMap
import HilbertSmithPaper.LTheory.Base.Complexes.StructureInvolution
import HilbertSmithPaper.LTheory.Base.Complexes.StructurePush
import HilbertSmithPaper.LTheory.Base.Complexes.SumOfComplexes
import HilbertSmithPaper.LTheory.Base.Complexes.StructurePushInvolution
import HilbertSmithPaper.LTheory.Base.Pairs.PairMap
import HilbertSmithPaper.LTheory.Base.Pairs.SymmetricPoincareComplex
import HilbertSmithPaper.LTheory.Base.Pairs.FunctorPoincare

/-!
# The paper

The Lean side of the paper in `blueprint/roadmap/paper/`: every formalizable article there names
one declaration of this library in its `lean:` field, and states exactly what that declaration
states. Declarations live in the namespace `HSP`.

This library imports only Mathlib and TauCeti.
-/
