import HilbertSmithPaper.LTheory.Ultimate.Groups.InducedMapLevel
import HilbertSmithPaper.LTheory.Base.Categories.DualityFunctors.CompositeDualityFunctor
import HilbertSmithPaper.LTheory.Ultimate.Groups.LevelExhaustive
import HilbertSmithPaper.LTheory.Base.Groups.LpMapComp
import HilbertSmithPaper.LTheory.Bounded.Categories.BoundedFunctorComp

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
  ext y
  obtain ⟨j, x, rfl⟩ := ultL.exists_of A k y
  have hFG := DFunLike.congr_fun (ultL.map_of (F.comp G) k j) x
  have hF := DFunLike.congr_fun (ultL.map_of F k j) x
  have hG := DFunLike.congr_fun (ultL.map_of G k j) (Lp.map (Bounded.mapIter F j) (k + j) x)
  simp only [AddMonoidHom.comp_apply] at hFG hF hG ⊢
  rw [hFG, hF, hG, (Bounded.mapIter_id_comp F G j).2, Lp.map_comp, AddMonoidHom.comp_apply]

end HSP
