import Mathlib
import HilbertSmithPaper.Corner.Theorem.ScalarForget

/-!
# Forgetting to the scalar exterior quotient is strict

The functor `U^𝐆 : ℬ_{𝐆,T×Z₀}(T × S^n) → ℬ_{𝟏,Z₀}(S^n)` induced by forgetting the control space
is a strict duality functor: it commutes with the dualities on objects and its duality
isomorphism is the identity.

## Encoding

`HSP.Corner.scalarForget_isStrict` (the declaration of the article). `scalarForget` is the
first component of the induced functor `HSP.extFunctor` on exterior quotients, built from the
strictness of `forgetControl` (`HSP.forgetControl_isStrict`); the second component of
`extFunctor` records strictness of the induced functor, and the proof reads it off from there (by
unfolding, since the shared construction in the `ScalarForget` module is private).
-/

open CategoryTheory

namespace HSP.Corner

variable (n : ℕ) (R : ℝ) {p : ℕ} (T : Type*) [MetricSpace T] [CompactSpace T]
  [AddAction (ZMod p) T] (G : GroupSeq p)

/-- **Forgetting to the scalar exterior quotient is strict**: `U^𝐆` is a strict duality
functor. -/
theorem scalarForget_isStrict : (scalarForget n R T G).IsStrict :=
  (extFunctor (forgetControl (G := G) T (RoundSphere n)) (forgetControl_isStrict T (RoundSphere n))
    (fun _ hP => forgetControl_supp (fun _ _ => rfl) hP)).2.1

end HSP.Corner
