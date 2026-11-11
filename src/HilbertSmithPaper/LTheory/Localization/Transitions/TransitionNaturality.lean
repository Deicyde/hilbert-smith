import HilbertSmithPaper.LTheory.Localization.Transitions.TransitionMap
import HilbertSmithPaper.LTheory.Base.Groups.InducedMap
import HilbertSmithPaper.LTheory.Bounded.Categories.BoundedFunctor

/-!
# Naturality of the transition

For a duality functor `(F, ξ) : A → A'` and `j ≥ 0`, with `C_{ℤ^j} F` its `j`-fold bounded
extension, `t ∘ (C_{ℤ^j} F)_* = (C_{ℤ^{j+1}} F)_* ∘ t : L^p_m(C_{ℤ^j} A) → L^p_{m+1}(C_{ℤ^{j+1}} A')`.
-/

namespace HSP

universe v₁ v₂ u₁ u₂

variable {A : Type u₁} [CategoryTheory.Category.{v₁} A] [CategoryTheory.Preadditive A]
  [CategoryTheory.Linear ℚ A] [CategoryTheory.Limits.HasFiniteBiproducts A] [DualCat A]
  {A' : Type u₂} [CategoryTheory.Category.{v₂} A'] [CategoryTheory.Preadditive A']
  [CategoryTheory.Linear ℚ A'] [CategoryTheory.Limits.HasFiniteBiproducts A'] [DualCat A']

/-- `t ∘ (C_{ℤ^j} F)_* = (C_{ℤ^{j+1}} F)_* ∘ t`. -/
theorem transitionMap_natural (F : DualFunctor A A') (j : ℕ) {m m' : ℤ} (hm : m + 1 = m') :
    (transitionMap A' j hm).comp (Lp.map (Bounded.mapIter F j) m) =
      (Lp.map (Bounded.mapIter F (j + 1)) m').comp (transitionMap A j hm) := by
  sorry

end HSP
