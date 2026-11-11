import Mathlib
import HilbertSmithPaper.Categories.Asymptotic.Structure.EmptyObject
import HilbertSmithPaper.Categories.Asymptotic.Structure.ClassSurjective

/-!
# The empty sequence is a zero object

`⟨(0, ∅)⟩` is a zero object of `𝒜_𝐆(X)` (`HSP.AsymCat.isZero_zero`): every sequence of matrices to
or from the empty sequence is zero, and every morphism is a class.
-/

open CategoryTheory CategoryTheory.Limits Filter Topology
open scoped NNReal

namespace HSP

variable {p : ℕ} {G : GroupSeq p} {X : Type*} [MetricSpace X] [AddAction (ZMod p) X]

private theorem hom_zero_eq {N : AsymPre G X} (u : (AsymPre.zero : AsymPre G X) ⟶ N) : u = 0 :=
  AsymPre.hom_ext fun _ => FreeCat.hom_ext (Matrix.ext fun _ b => b.2.elim0)

private theorem zero_hom_eq {M : AsymPre G X} (u : M ⟶ (AsymPre.zero : AsymPre G X)) : u = 0 :=
  AsymPre.hom_ext fun _ => FreeCat.hom_ext (Matrix.ext fun a _ => a.2.elim0)

/-- The empty sequence is a zero object of `𝒜_𝐆(X)`. -/
theorem AsymCat.isZero_zero : IsZero (⟨AsymPre.zero⟩ : AsymCat G X) := by
  refine ⟨fun Y => ⟨⟨⟨0⟩, fun f => ?_⟩⟩, fun Y => ⟨⟨⟨0⟩, fun f => ?_⟩⟩⟩
  · obtain ⟨u, rfl⟩ := AsymCat.mkHom_surjective f
    rw [hom_zero_eq u]
    exact (Quotient.functor (asymRel G X)).map_zero _ _
  · obtain ⟨u, rfl⟩ := AsymCat.mkHom_surjective f
    rw [zero_hom_eq u]
    exact (Quotient.functor (asymRel G X)).map_zero _ _

end HSP
