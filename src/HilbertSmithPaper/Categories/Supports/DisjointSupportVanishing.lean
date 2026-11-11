import HilbertSmithPaper.Categories.Supports.SupportIdeal
import HilbertSmithPaper.Categories.Supports.ThickeningInvariant

/-!
# Maps through a disjoint support vanish

Let `X` be compact with an isometric `C_p`-action, and let `S, Z ⊆ X` be disjoint, closed and
invariant. A map `[u] : M → N` of `𝒜_𝐆(X)` into an `S`-supported object that factors through an
object of `𝒜_Z` is zero (`HSP.mkHom_eq_zero_of_disjoint`): disjoint compact and closed sets have
disjoint `δ`-thickenings, and by the support ideal every nonzero entry of `u_i` eventually has its
row label near both `S` and `Z`.
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
  exact Set.disjoint_left.1 hdisj ((vadd_mem_thickening_iff hSi _).2 (hNi a.2)) (hi a b hab).1

end HSP
