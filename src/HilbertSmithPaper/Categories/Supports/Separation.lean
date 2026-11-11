import HilbertSmithPaper.Categories.Supports.DisjointSupportVanishing
import HilbertSmithPaper.LTheory.Base.Categories.DualSubcategory

/-!
# Separation

Let `X` be compact with an isometric `C_p`-action, and let `S, Z ⊆ X` be disjoint, closed and
invariant. The quotient functor restricted to `𝒜_S`, `ι ⋙ q : 𝒜_S → 𝒜_𝐆(X)/𝒜_Z`, is full and
faithful (`HSP.separation`). Faithfulness rests on `HSP.mkHom_eq_zero_of_disjoint`.
-/

open CategoryTheory CategoryTheory.Limits Filter Metric

namespace HSP

variable {p : ℕ} {G : GroupSeq p} {X : Type*} [MetricSpace X] [AddAction (ZMod p) X]
  [IsIsometricVAdd (ZMod p) X]

/-- **Separation.** For disjoint closed invariant `S, Z` in a compact `X` with an isometric
action, the quotient functor restricted to `𝒜_S`, `𝒜_S → 𝒜_𝐆(X)/𝒜_Z`, is full and faithful. -/
theorem separation [CompactSpace X] {S Z : Set X} (hS : IsClosed S) (hZ : IsClosed Z)
    (hSi : ∀ c : ZMod p, ∀ x ∈ S, c +ᵥ x ∈ S) (hZi : ∀ c : ZMod p, ∀ x ∈ Z, c +ᵥ x ∈ Z)
    (hSZ : Disjoint S Z) :
    ((supp S : ObjectProperty (AsymCat G X)).ι ⋙ FiltQuot.functor (supp Z)).Full ∧
      ((supp S : ObjectProperty (AsymCat G X)).ι ⋙ FiltQuot.functor (supp Z)).Faithful := by
  refine ⟨inferInstance, ⟨fun {M N} f g hfg => ?_⟩⟩
  simp only [Functor.comp_map, ObjectProperty.ι_map] at hfg
  rw [FiltQuot.functor_map_eq_iff] at hfg
  obtain ⟨w, hw⟩ := AsymCat.mkHom_surjective (f.hom - g.hom)
  rw [← hw] at hfg
  have h0 := mkHom_eq_zero_of_disjoint hS hZ hSi hZi hSZ N.property w hfg
  refine ObjectProperty.hom_ext _ (sub_eq_zero.1 ?_)
  rw [← hw, h0]

end HSP
