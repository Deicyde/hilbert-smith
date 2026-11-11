import HilbertSmithPaper.Categories.Supports.SupportFiltration
import HilbertSmithPaper.LTheory.Base.Categories.FiltrationQuotient

/-!
# Support filtrations in a quotient

For `S, Z, Y ⊆ X`, `𝒰_Y` (`HSP.quotSupp S Z Y`) is the predicate "`Y`-supported" on the objects of
`𝒜_S/𝒜_Z = FiltQuot (suppIn S Z)`. It is a full additive subcategory closed under duality
(`HSP.isDualAdditive_quotSupp`: the images under the additive quotient functor `q` of a zero object
and of the biproducts of `𝒜_Y ⊂ 𝒜_S`). If the action is isometric and `Y` is invariant, it is an
involution-invariant Karoubi filtration (`HSP.quotSupp_karoubiFiltration`) whose chosen
decompositions of `⟨M⟩` are the images `q(p)` of the chosen decompositions `p` of `M` in the support
filtration for `Y` (`HSP.supp_karoubiFiltration`). No disjointness of `Y` and `Z`, and no
inclusion `Y, Z ⊆ S`, is used. `𝒰_Y` is not closed under isomorphism.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

open DualCat

variable {p : ℕ} {G : GroupSeq p} {X : Type*} [MetricSpace X] [AddAction (ZMod p) X]

/-- `𝒰_Y ⊂ 𝒜_S/𝒜_Z`: the objects `⟨M⟩` with `M` `Y`-supported. -/
abbrev quotSupp (S Z Y : Set X) : ObjectProperty (FiltQuot (suppIn (G := G) S Z)) :=
  fun M => supp Y M.as.obj

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

/-- In `𝒜_S/𝒜_Z` the duality is an involution on the nose on morphisms. -/
private theorem dualHom_dualHom_quot {S Z : Set X} {M N : FiltQuot (suppIn (G := G) S Z)}
    (q : M ⟶ N) : dualHom (dualHom q) = q := by
  obtain ⟨w, rfl⟩ := FiltQuot.functor_map_surjective (suppIn S Z) q
  rw [FiltQuot.dualHom_map, FiltQuot.dualHom_map]
  congr 1
  refine ObjectProperty.hom_ext _ ?_
  obtain ⟨u, hu⟩ := AsymCat.mkHom_surjective w.hom
  change dualHom (dualHom w.hom) = w.hom
  rw [← hu, AsymCat.dualHom_mkHom, AsymCat.dualHom_mkHom, AsymPre.transpose_transpose]

variable [IsIsometricVAdd (ZMod p) X]

/-- **Support filtrations in a quotient.** For an isometric action and an invariant `Y`, `𝒰_Y` is
an involution-invariant Karoubi filtration of `𝒜_S/𝒜_Z`, whose chosen decompositions are the images
of the chosen decompositions of the support filtration for `Y` in `𝒜_S`. -/
noncomputable def quotSupp_karoubiFiltration (S Z : Set X) {Y : Set X}
    (hY : ∀ c : ZMod p, ∀ x ∈ Y, c +ᵥ x ∈ Y) : KaroubiFiltration (quotSupp (G := G) S Z Y) where
  D M := (FiltQuot.functor (suppIn S Z)).map '' (supp_karoubiFiltration S hY).D M.as
  idem := by
    rintro M _ ⟨p, hp, rfl⟩
    rw [← Functor.map_comp, (supp_karoubiFiltration S hY).idem hp]
  split := by
    rintro M _ ⟨p, hp, rfl⟩
    obtain ⟨E, hE, i, r, h1, h2⟩ := (supp_karoubiFiltration S hY).split hp
    exact ⟨(FiltQuot.functor _).obj E, hE, (FiltQuot.functor _).map i,
      (FiltQuot.functor _).map r, by rw [← Functor.map_comp, h1, CategoryTheory.Functor.map_id],
      by rw [← Functor.map_comp, h2]⟩
  split_compl := by
    rintro M _ ⟨p, hp, rfl⟩
    obtain ⟨E, i, r, h1, h2⟩ := (supp_karoubiFiltration S hY).split_compl hp
    exact ⟨(FiltQuot.functor _).obj E, (FiltQuot.functor _).map i,
      (FiltQuot.functor _).map r, by rw [← Functor.map_comp, h1, CategoryTheory.Functor.map_id],
      by rw [← Functor.map_comp, h2, Functor.map_sub, CategoryTheory.Functor.map_id]; rfl⟩
  nonempty M := by
    obtain ⟨p, hp⟩ := (supp_karoubiFiltration S hY).nonempty M.as
    exact ⟨_, p, hp, rfl⟩
  directed := by
    rintro M _ _ ⟨p, hp, rfl⟩ ⟨p', hp', rfl⟩
    obtain ⟨p'', hp'', ⟨h1, h2⟩, h3, h4⟩ := (supp_karoubiFiltration S hY).directed hp hp'
    refine ⟨_, ⟨p'', hp'', rfl⟩, ⟨?_, ?_⟩, ?_, ?_⟩ <;> rw [← Functor.map_comp]
    exacts [congrArg _ h1, congrArg _ h2, congrArg _ h3, congrArg _ h4]
  factor_left := by
    intro V M g hV
    obtain ⟨g, rfl⟩ := FiltQuot.functor_map_surjective (suppIn S Z) g
    obtain ⟨p, hp, h⟩ := (supp_karoubiFiltration S hY).factor_left g hV
    exact ⟨_, ⟨p, hp, rfl⟩, by rw [← Functor.map_comp, h]⟩
  factor_right := by
    intro M V g hV
    obtain ⟨g, rfl⟩ := FiltQuot.functor_map_surjective (suppIn S Z) g
    obtain ⟨p, hp, h⟩ := (supp_karoubiFiltration S hY).factor_right g hV
    exact ⟨_, ⟨p, hp, rfl⟩, by rw [← Functor.map_comp, h]⟩
  dual_mem_iff := by
    intro M q
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨dualHom p, ((supp_karoubiFiltration S hY).dual_mem_iff p).1 hp,
        (FiltQuot.dualHom_map _ p).symm⟩
    · rintro ⟨p, hp, hpq⟩
      refine ⟨dualHom p, ((supp_karoubiFiltration S hY).dual_mem_iff p).1 hp, ?_⟩
      rw [← FiltQuot.dualHom_map, hpq, dualHom_dualHom_quot]

/-- Non-vacuity: the quotient support filtration for `Y = ∅`. -/
private noncomputable def quotSupp_karoubiFiltration_empty (S Z : Set X) :
    KaroubiFiltration (quotSupp (G := G) S Z (∅ : Set X)) :=
  quotSupp_karoubiFiltration S Z fun _ _ h => h.elim

end HSP
