import Mathlib
import HilbertSmithPaper.LTheory.Base.Categories.DualityFunctors.StrictDualityFunctor
import HilbertSmithPaper.LTheory.Base.Categories.DualityFunctors.CompositeDualityFunctor
import HilbertSmithPaper.Categories.Functors.ForgetControl

/-!
# Forgetting the control space is strict

Forgetting the control space `U_c = U ∘ pr_* : 𝒜_𝐆(T × X) → 𝒜_𝟏(X)` is a strict duality functor:
`U_c (M^*) = (U_c M)^*` and its duality isomorphism is the identity. Both factors, the pushforward
`pr_*` and forgetting the group `U`, have identity duality isomorphisms and commute with the
dualities on objects, so their composite does.

## Encoding

`HSP.forgetControl_isStrict` (the declaration of the article), proved by unfolding the composite.
-/

open CategoryTheory

namespace HSP

variable {p : ℕ} {G : GroupSeq p}
  (T : Type*) [MetricSpace T] [CompactSpace T] [AddAction (ZMod p) T]
  (X : Type*) [MetricSpace X] [CompactSpace X] [AddAction (ZMod p) X]

/-- **Forgetting the control space is strict**: `U_c` is a strict duality functor. -/
theorem forgetControl_isStrict : (forgetControl (G := G) T X).IsStrict :=
  fun _ => ⟨rfl, by simp [forgetControl, DualFunctor.comp, push, forgetGroup]; rfl⟩

end HSP
