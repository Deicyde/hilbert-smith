import HilbertSmithPaper.LTheory.Localization.Transitions.TransitionMap

/-!
# Sequence of lower L-groups

The diagram `L^{⟨0⟩}_k(A) → L^{⟨-1⟩}_k(A) → L^{⟨-2⟩}_k(A) → ⋯` of abelian groups over `(ℕ, ≤)`,
of the lower L-groups and the transition maps; the map from stage `j` to stage `j' ≥ j` is the
composite of the transitions between them (`Functor.ofSequence`).
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

universe v u

variable (A : Type u) [Category.{v} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A]

/-- The sequence `L^{⟨0⟩}_k(A) → L^{⟨-1⟩}_k(A) → ⋯` of lower L-groups and transition maps. -/
noncomputable def lowerLSeq (k : ℤ) : ℕ ⥤ AddCommGrpCat.{max u v} :=
  Functor.ofSequence fun j => AddCommGrpCat.ofHom (transitionLower A j k)

end HSP
