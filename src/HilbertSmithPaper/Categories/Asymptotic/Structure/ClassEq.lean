import Mathlib
import HilbertSmithPaper.Categories.Asymptotic.AsymptoticCategory

/-!
# Equality of classes

Two sequences `u, v : M → N` have the same class, `[u] = [v]`, exactly when `u_i = v_i` for all
large `i` (`HSP.AsymCat.mkHom_eq_iff`).
-/

open CategoryTheory CategoryTheory.Limits Filter Topology
open scoped NNReal

namespace HSP

variable {p : ℕ} {G : GroupSeq p} {X : Type*} [MetricSpace X] [AddAction (ZMod p) X]

/-- `[u] = [v]` if and only if `u_i = v_i` eventually. -/
theorem AsymCat.mkHom_eq_iff {M N : AsymPre G X} (u v : M ⟶ N) :
    AsymCat.mkHom u = AsymCat.mkHom v ↔ ∀ᶠ i in atTop, AsymPre.coord u i = AsymPre.coord v i :=
  Quotient.functor_map_eq_iff _ u v

end HSP
