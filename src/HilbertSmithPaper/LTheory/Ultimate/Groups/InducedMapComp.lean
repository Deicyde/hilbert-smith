import HilbertSmithPaper.LTheory.Ultimate.Groups.InducedMap

/-!
# Functoriality on ultimate L

For duality functors `F : A → B` and `G : B → C`, `(G ∘ F)_* = G_* ∘ F_*` on `𝕃_k`.

Lean: `A`, `B`, `C` have the same universe levels, as for the induced map.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

universe v u

variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A]
  {B : Type u} [Category.{v} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B]
  {E : Type u} [Category.{v} E] [Preadditive E] [Linear ℚ E] [HasFiniteBiproducts E]
  [DualCat E]

/-- `(G ∘ F)_* = G_* ∘ F_*` on `𝕃_k`. -/
theorem ultL.map_comp (F : DualFunctor A B) (G : DualFunctor B E) (k : ℤ) :
    ultL.map (F.comp G) k = (ultL.map G k).comp (ultL.map F k) := by
  sorry

end HSP
