import HilbertSmithPaper.LTheory.Ultimate.Groups.InducedMapLevel
import HilbertSmithPaper.LTheory.Ultimate.Groups.LevelExhaustive
import HilbertSmithPaper.LTheory.Ultimate.Groups.BoundedSumExtension
import HilbertSmithPaper.LTheory.Base.Groups.LpMapBiprod
import HilbertSmithPaper.LTheory.Base.Groups.LpMapUnitary

/-!
# Additivity on ultimate L

For duality functors `F, G : A → B`, `(F ⊕ G)_* = F_* + G_*` on `𝕃_k(A)`: at each stage `j`,
`C_{ℤ^j}(F ⊕ G) ≅ C_{ℤ^j} F ⊕ C_{ℤ^j} G` unitarily, so the induced maps on `L^p` add.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

universe v u

variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A]
  {B : Type u} [Category.{v} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B]

/-- **Additivity on ultimate L.** `(F ⊕ G)_* = F_* + G_*` on `𝕃_k(A)`. -/
theorem ultL.map_biprod (F G : DualFunctor A B) (k : ℤ) :
    ultL.map (F.biprod G) k = ultL.map F k + ultL.map G k := by
  ext y
  obtain ⟨j, x, rfl⟩ := ultL.exists_of A k y
  have hS := DFunLike.congr_fun (ultL.map_of (F.biprod G) k j) x
  have hF := DFunLike.congr_fun (ultL.map_of F k j) x
  have hG := DFunLike.congr_fun (ultL.map_of G k j) x
  simp only [AddMonoidHom.comp_apply] at hS hF hG
  rw [AddMonoidHom.add_apply, hS, hF, hG, Lp.map_eq_of_unitaryIso (Bounded.sumIsoIter F G j),
    Lp.map_biprod, AddMonoidHom.add_apply, map_add]

end HSP
