import Mathlib
import HilbertSmithPaper.Categories.Functors.ForgetLabels

/-!
# Forgetting labels is strict

Forgetting labels `Φ : 𝒜_𝐆(X) → 𝒱_𝐆` is a strict duality functor: `Φ(M^*) = Φ(M)^*` and its
duality isomorphism is the identity, because `Φ` keeps the ranks and transposes commute with the
quotient functor `q`.

## Encoding

`HSP.forgetLabels_isStrict` (the declaration of the article), by unfolding.
-/

open CategoryTheory

namespace HSP

variable {p : ℕ} {G : GroupSeq p} {X : Type*} [MetricSpace X] [AddAction (ZMod p) X]

/-- **Forgetting labels is strict**: `Φ` is a strict duality functor. -/
theorem forgetLabels_isStrict : (forgetLabels (G := G) (X := X)).IsStrict :=
  fun _ => ⟨rfl, rfl⟩

end HSP
