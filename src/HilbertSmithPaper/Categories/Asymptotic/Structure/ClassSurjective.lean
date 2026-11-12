import Mathlib
import HilbertSmithPaper.Categories.Asymptotic.AsymptoticCategory

/-!
# Every morphism is a class

Every morphism `f : ⟨M⟩ → ⟨N⟩` of `𝒜_𝐆(X)` is the class `[u]` of a sequence `u : M → N`
(`HSP.AsymCat.mkHom_surjective`).
-/

open CategoryTheory CategoryTheory.Limits Filter Topology
open scoped NNReal

namespace HSP

variable {p : ℕ} {G : GroupSeq p} {X : Type*} [MetricSpace X] [AddAction (ZMod p) X]

/-- Every morphism of `𝒜_𝐆(X)` is a class `[u]`. -/
theorem AsymCat.mkHom_surjective {P Q : AsymCat G X} (f : P ⟶ Q) :
    ∃ u : P.as ⟶ Q.as, AsymCat.mkHom u = f :=
  (Quotient.functor (asymRel G X)).map_surjective f

end HSP
