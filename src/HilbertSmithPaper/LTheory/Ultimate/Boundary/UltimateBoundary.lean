import HilbertSmithPaper.LTheory.Localization.Transitions.TransitionBoundaryCommute
import HilbertSmithPaper.LTheory.Ultimate.Groups.LevelCompatible
import HilbertSmithPaper.LTheory.Base.Groups.LGroupCast

/-!
# Ultimate boundary

For an involution-invariant Karoubi filtration `𝒰 ⊂ 𝒜`, `∂ : 𝕃_k(𝒜/𝒰) → 𝕃_{k-1}(𝒰)` is the
homomorphism out of the colimit given at stage `j` by `x ↦ ι_{j+1} (∂^{(j)} x)`, with `∂^{(j)}` the
stage boundary. These maps are compatible with `t` because `ι_{j+1} ∂^{(j)} x = ι_{j+2} t ∂^{(j)} x
= ι_{j+2} ∂^{(j+1)} t x`.

This definition rests on the open statement Lifting, through the stage boundaries.

Lean: `∂^{(j)}` is read in `L^{⟨-j-1⟩}_{k-1}(𝒰)` through `Bounded.subPowIdent` and the transport
of degrees, as in `transitionLower_levelBoundary`.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents

namespace HSP

universe v u

variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A] {U : ObjectProperty A} [IsDualAdditive U]

/-- The stage boundary `∂^{(j)} : L^{⟨-j⟩}_k(𝒜/𝒰) → L^{⟨-j-1⟩}_{k-1}(𝒰)`. -/
private noncomputable def stageBoundary (F : KaroubiFiltration U) (j : ℕ) (k : ℤ) :
    lowerL (FiltQuot U) j k →+ lowerL U.FullSubcategory (j + 1) (k - 1) :=
  (LGroup.castIndex (B := Karoubi (BoundedPow U.FullSubcategory (j + 1)))
    (show k + j + 1 - 1 = k - 1 + ((j + 1 : ℕ) : ℤ) by push_cast; ring)).toAddMonoidHom.comp
    ((Lp.map (Bounded.subPowIdent U (j + 1)) (k + j + 1 - 1)).comp (levelBoundary F j k))

/-- The cocone `x ↦ ι_{j+1} (∂^{(j)} x)` on the sequence of lower L-groups of `𝒜/𝒰`. -/
private noncomputable def boundaryCocone (F : KaroubiFiltration U) (k : ℤ) :
    Cocone (lowerLSeq (FiltQuot U) k) where
  pt := colimit (lowerLSeq U.FullSubcategory (k - 1))
  ι := NatTrans.ofSequence (fun j => AddCommGrpCat.ofHom
    ((ultL.of U.FullSubcategory (k - 1) (j + 1)).comp (stageBoundary F j k))) (by
      intro j
      have e : (lowerLSeq (FiltQuot U) k).map (homOfLE (Nat.le_add_right j 1)) =
          AddCommGrpCat.ofHom (transitionLower (FiltQuot U) j k) :=
        Functor.ofSequence_map_homOfLE_succ _ j
      rw [e]
      ext x
      change ultL.of U.FullSubcategory (k - 1) (j + 1 + 1)
          (stageBoundary F (j + 1) k (transitionLower (FiltQuot U) j k x)) =
        ultL.of U.FullSubcategory (k - 1) (j + 1) (stageBoundary F j k x)
      have h := transitionLower_levelBoundary F j k x
      change transitionLower U.FullSubcategory (j + 1) (k - 1) (stageBoundary F j k x) =
        stageBoundary F (j + 1) k (transitionLower (FiltQuot U) j k x) at h
      rw [← h]
      exact congrArg (fun f => f (stageBoundary F j k x))
        ((ultL.of_trans U.FullSubcategory (k - 1)).1 (j + 1)))

/-- The ultimate boundary `∂ : 𝕃_k(𝒜/𝒰) → 𝕃_{k-1}(𝒰)`. -/
noncomputable def ultBoundary (F : KaroubiFiltration U) (k : ℤ) :
    ultL (FiltQuot U) k →+ ultL U.FullSubcategory (k - 1) :=
  (colimit.desc (lowerLSeq (FiltQuot U) k) (boundaryCocone F k)).hom

end HSP
