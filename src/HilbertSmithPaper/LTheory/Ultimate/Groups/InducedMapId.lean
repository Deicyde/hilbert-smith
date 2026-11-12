import HilbertSmithPaper.LTheory.Ultimate.Groups.InducedMapLevel
import HilbertSmithPaper.LTheory.Ultimate.Groups.LevelExhaustive
import HilbertSmithPaper.LTheory.Base.Groups.LpMapId
import HilbertSmithPaper.LTheory.Bounded.Categories.BoundedFunctorComp

/-!
# Identity on ultimate L

`(id_A)_* = id` on `𝕃_k(A)`: `C_{ℤ^j}(id_A) = id`, so at stage `j` both sides agree by the
identity on L^p and the induced map at each stage, and every element comes from a finite stage.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

universe v u

variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A]

/-- `(id_A)_* = id` on `𝕃_k(A)`. -/
theorem ultL.map_id (k : ℤ) : ultL.map (DualFunctor.id A) k = AddMonoidHom.id _ := by
  ext y
  obtain ⟨j, x, rfl⟩ := ultL.exists_of A k y
  have h := DFunLike.congr_fun (ultL.map_of (DualFunctor.id A) k j) x
  simp only [AddMonoidHom.comp_apply] at h
  rw [AddMonoidHom.id_apply, h,
    (Bounded.mapIter_id_comp (DualFunctor.id A) (DualFunctor.id A) j).1, Lp.map_id,
    AddMonoidHom.id_apply]

end HSP
