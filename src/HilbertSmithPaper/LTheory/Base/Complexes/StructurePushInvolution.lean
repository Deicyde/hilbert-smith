import HilbertSmithPaper.LTheory.Base.Complexes.StructureInvolution
import HilbertSmithPaper.LTheory.Base.Complexes.StructurePush

/-!
# Pushforward commutes with T

`g_% T = T g_%` for a chain map `g : C ⟶ D`: `(g f g^*)^* = g^{**} f^* g^* = g f^* g^*`.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

open DualCat

universe v u

variable {B : Type u} [Category.{v} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B]

/-- Pushforward commutes with the involution: `T ∘ g_% = g_% ∘ T`. -/
theorem StructureCx.push_T {C D : ChainComplex B ℤ} (g : C ⟶ D) :
    StructureCx.T C ≫ StructureCx.push g = StructureCx.push g ≫ StructureCx.T D := by
  ext n f : 3
  refine funext fun x => ?_
  obtain ⟨⟨p, q⟩, hpq⟩ := x
  change ((StructureCx.push g).f n ((StructureCx.T C).f n f)) ⟨(p, q), hpq⟩ =
    ((StructureCx.T D).f n ((StructureCx.push g).f n f)) ⟨(p, q), hpq⟩
  rw [StructureCx.push_apply, StructureCx.T_apply, StructureCx.T_apply, StructureCx.push_apply]
  simp only [dualHom_comp, dualHom_dualHom, Category.assoc, Linear.units_smul_comp,
    Linear.comp_units_smul, eqToHom_trans, eqToHom_refl, Category.comp_id]

end HSP
