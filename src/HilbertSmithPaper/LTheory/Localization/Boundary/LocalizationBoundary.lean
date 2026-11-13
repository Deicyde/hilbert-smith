import Mathlib
import HilbertSmithPaper.LTheory.Localization.Boundary.BoundaryIndependence
import HilbertSmithPaper.LTheory.Localization.Boundary.LiftToPairClosed
import HilbertSmithPaper.LTheory.Localization.Boundary.UPairSum

/-!
# Localization boundary

For an involution-invariant Karoubi filtration `𝒰 ⊂ 𝒜` and `x ∈ L^{im}_k(𝒜/𝒰)`, choose a strict
`k`-dimensional `𝒰`-pair `V_x` over `(P_x, π_x)` with `[q V_x] = x`. The localization boundary is
the homomorphism `∂ : L^{im}_k(𝒜/𝒰) → L^p_{k-1}(𝒰)`, `x ↦ [P_x, π_x]`; it does not depend on the
choice, by independence of the lift, and it is additive by sums of `𝒰`-pairs.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

universe v u

variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A] {U : ObjectProperty A} [IsDualAdditive U]

/-- **Localization boundary.** `∂ : L^{im}_k(𝒜/𝒰) → L^p_{k-1}(𝒰)`, `x ↦ [P_x, π_x]` for a
`𝒰`-pair `V_x` over `(P_x, π_x)` with `[q V_x] = x`. -/
noncomputable def locBoundary (F : KaroubiFiltration U) (k : ℤ) :
    LIm U k →+ Lp U.FullSubcategory (k - 1) :=
  AddMonoidHom.mk' (fun x => LGroup.mk (UPair.exists_image_eq F x).choose.P) fun x y => by
    obtain ⟨V, h1, h2⟩ := UPair.exists_add (UPair.exists_image_eq F x).choose
      (UPair.exists_image_eq F y).choose
    rw [← h2]
    refine UPair.mk_P_eq_of_image F _ _ ?_
    rw [h1, (UPair.exists_image_eq F x).choose_spec, (UPair.exists_image_eq F y).choose_spec,
      (UPair.exists_image_eq F (x + y)).choose_spec]

/-- `∂ x = [P, π]` for any `𝒰`-pair `V` over `(P, π)` with `[q V] = x`. -/
private lemma locBoundary_eq (F : KaroubiFiltration U) {k : ℤ} (V : UPair U k) :
    locBoundary F k (LGroup.mk V.image) = LGroup.mk V.P :=
  UPair.mk_P_eq_of_image F _ _ (UPair.exists_image_eq F _).choose_spec

end HSP
