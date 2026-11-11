import Mathlib

/-!
# Bounded complexes have finitely many nonzero chain objects

A complex indexed by `ℤ` whose chain objects are zero objects outside `[0, k]` has only finitely
many chain objects that are not zero objects.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

/-- **Bounded complexes have finitely many nonzero chain objects.** -/
lemma finite_of_bounded {B : Type*} [Category B] [Preadditive B] {C : ChainComplex B ℤ} {k : ℤ}
    (h : ∀ r : ℤ, r < 0 ∨ k < r → IsZero (C.X r)) : {r | ¬ IsZero (C.X r)}.Finite :=
  (Set.finite_Icc 0 k).subset fun r hr => by
    by_contra h'
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at h'
    exact hr (h r (by omega))

end HSP
