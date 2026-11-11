import HilbertSmithPaper.Categories.Supports.SupportIdeal
import HilbertSmithPaper.LTheory.Base.Categories.DualSubcategory

/-!
# Separation

Let `X` be compact with an isometric `C_p`-action, and let `S, Z ⊆ X` be disjoint, closed and
invariant. The quotient functor restricted to `𝒜_S`, `ι ⋙ q : 𝒜_S → 𝒜_𝐆(X)/𝒜_Z`, is full and
faithful (`HSP.separation`). Faithfulness rests on `HSP.mkHom_eq_zero_of_disjoint`: a map into an
`S`-supported object that factors through `𝒜_Z` is zero, because disjoint compact and closed sets
have disjoint `δ`-thickenings, and by the support ideal every nonzero entry eventually has its row
label near both `S` and `Z`.
-/

open CategoryTheory CategoryTheory.Limits Filter Metric

namespace HSP

variable {p : ℕ} {G : GroupSeq p} {X : Type*} [MetricSpace X] [AddAction (ZMod p) X]
  [IsIsometricVAdd (ZMod p) X]

/-- A map into an `S`-supported object factoring through `𝒜_Z`, with `S, Z` disjoint, closed and
invariant in a compact `X`, is zero. -/
theorem mkHom_eq_zero_of_disjoint [CompactSpace X] {S Z : Set X} (hS : IsClosed S)
    (hZ : IsClosed Z) (hSi : ∀ c : ZMod p, ∀ x ∈ S, c +ᵥ x ∈ S)
    (hZi : ∀ c : ZMod p, ∀ x ∈ Z, c +ᵥ x ∈ Z) (hSZ : Disjoint S Z) {M N : AsymPre G X}
    (hN : supp S (⟨N⟩ : AsymCat G X)) (u : M ⟶ N)
    (hu : FiltQuot.ideal (supp Z) (AsymCat.mkHom u)) : AsymCat.mkHom u = 0 := by
  obtain ⟨δ, hδ, hdisj⟩ := hSZ.exists_thickenings hS.isCompact hZ
  have h := (factorsThrough_supp_iff hZi u).1 hu δ hδ
  rw [← CategoryTheory.Functor.map_zero (Quotient.functor (asymRel G X)) M N,
    AsymCat.mkHom_eq_iff]
  filter_upwards [h, hN δ hδ] with i hi hNi
  refine FreeCat.hom_ext (Matrix.ext fun a b => ?_)
  by_contra hab
  exact Set.disjoint_left.1 hdisj (vadd_mem_thickening hSi _ (hNi a.2)) (hi a b hab).1

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
