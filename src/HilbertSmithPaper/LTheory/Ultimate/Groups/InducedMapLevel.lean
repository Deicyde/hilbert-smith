import HilbertSmithPaper.LTheory.Ultimate.Groups.InducedMap

/-!
# The induced map at each stage

For a duality functor `F : A → A'` and every `j ≥ 0`, `F_* ∘ ι_j = ι_j ∘ (C_{ℤ^j} F)_*`.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

universe v u

variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A]
  {A' : Type u} [Category.{v} A'] [Preadditive A'] [Linear ℚ A'] [HasFiniteBiproducts A']
  [DualCat A']

/-- `F_* ∘ ι_j = ι_j ∘ (C_{ℤ^j} F)_*`. -/
theorem ultL.map_of (F : DualFunctor A A') (k : ℤ) (j : ℕ) :
    (ultL.map F k).comp (ultL.of A k j) =
      (ultL.of A' k j).comp (Lp.map (Bounded.mapIter F j) (k + j)) := by
  ext x
  change (colimit.ι (lowerLSeq A k) j ≫ colimMap _).hom x = _
  rw [ι_colimMap]
  rfl

end HSP
