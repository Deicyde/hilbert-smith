import HilbertSmithPaper.LTheory.Ultimate.Groups.UltimateLGroup
import HilbertSmithPaper.LTheory.Localization.Transitions.TransitionNaturality
import HilbertSmithPaper.LTheory.Bounded.Categories.BoundedFunctorIter

/-!
# Induced map on ultimate L

For a duality functor `(F, ξ) : A → A'`, not necessarily strict, with `j`-fold bounded extensions
`C_{ℤ^j} F` (`C_{ℤ^0} F = F`), `F_* : 𝕃_k(A) → 𝕃_k(A')` is the homomorphism of colimits induced
by the levelwise homomorphisms `(C_{ℤ^j} F)_* : L^{⟨-j⟩}_k(A) → L^{⟨-j⟩}_k(A')`, which commute
with `t` by naturality of the transition.

Lean: `A` and `A'` have the same universe levels, so that both colimits are taken in the same
category `AddCommGrpCat`.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

universe v u

variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A]
  {A' : Type u} [Category.{v} A'] [Preadditive A'] [Linear ℚ A'] [HasFiniteBiproducts A']
  [DualCat A']

/-- The levelwise maps `(C_{ℤ^j} F)_* : L^{⟨-j⟩}_k(A) → L^{⟨-j⟩}_k(A')`, a map of sequences. -/
private noncomputable def levelMap (F : DualFunctor A A') (k : ℤ) :
    lowerLSeq A k ⟶ lowerLSeq A' k :=
  NatTrans.ofSequence (fun j => AddCommGrpCat.ofHom (Lp.map (Bounded.mapIter F j) (k + j)))
    (by
      intro j
      simp only [lowerLSeq, Functor.ofSequence_map_homOfLE_succ]
      ext x
      exact congrArg (fun f => f x)
        (transitionMap_natural F j (m := k + j) (m' := k + ↑(j + 1)) (by push_cast; ring)).symm)

/-- The induced map `F_* : 𝕃_k(A) → 𝕃_k(A')` of the colimits. -/
noncomputable def ultL.map (F : DualFunctor A A') (k : ℤ) : ultL A k →+ ultL A' k :=
  (colimMap (levelMap F k)).hom

end HSP
