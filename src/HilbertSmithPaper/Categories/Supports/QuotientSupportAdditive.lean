import HilbertSmithPaper.Categories.Supports.QuotientSupport

/-!
# Supported objects of a support quotient are additive

`𝒰_Y ⊂ 𝒜_S/𝒜_Z` is a full additive subcategory closed under duality
(`HSP.isDualAdditive_quotSupp`): it contains the images under the additive quotient functor of a
zero object and of the biproducts of `𝒜_Y ⊂ 𝒜_S`, and `⟨M⟩^* = ⟨M⟩`.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

variable {p : ℕ} {G : GroupSeq p} {X : Type*} [MetricSpace X] [AddAction (ZMod p) X]

/-- `𝒰_Y` is a full additive subcategory of `𝒜_S/𝒜_Z` closed under duality. -/
instance isDualAdditive_quotSupp (S Z Y : Set X) : IsDualAdditive (quotSupp (G := G) S Z Y) where
  exists_zero := by
    obtain ⟨W, hW, hWz⟩ := IsDualAdditive.exists_zero (U := suppIn (G := G) S Y)
    exact ⟨(FiltQuot.functor _).obj W, hW, (FiltQuot.functor (suppIn S Z)).map_isZero hWz⟩
  exists_biprod {V W} hV hW := by
    obtain ⟨c, ⟨hc⟩, hpt⟩ := IsDualAdditive.exists_biprod (U := suppIn (G := G) S Y) hV hW
    refine ⟨(FiltQuot.functor (suppIn S Z)).mapBinaryBicone c,
      ⟨isBinaryBilimitOfTotal _ ?_⟩, hpt⟩
    have h := congrArg (FiltQuot.functor (suppIn S Z)).map (IsBilimit.binary_total hc)
    rw [CategoryTheory.Functor.map_add, Functor.map_comp, Functor.map_comp,
      CategoryTheory.Functor.map_id] at h
    exact h
  dual_mem h := h


end HSP
