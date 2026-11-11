import HilbertSmithPaper.LTheory.Base.Complexes.StructureInvolution

/-!
# T is an involution

`T² = 1` on `M(C)`: `f^{**} = f` and the sign `(-1)^{rs}` squares to `1`.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

open DualCat

universe v u

variable {B : Type u} [Category.{v} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B]

private lemma dualHom_units_smul'' {M N : B} (u : ℤˣ) (f : M ⟶ N) :
    dualHom (u • f) = u • dualHom f := by
  rw [Units.smul_def, Units.smul_def]
  exact (AddMonoidHom.mk' (dualHom (M := M) (N := N)) dualHom_add).map_zsmul (u : ℤ) f

/-- `T ∘ T = 1` on `M(C)`. -/
@[simp]
theorem StructureCx.T_sq (C : ChainComplex B ℤ) :
    StructureCx.T C ≫ StructureCx.T C = 𝟙 (StructureCx C) := by
  ext n f ⟨⟨p, q⟩, hpq⟩
  change ((StructureCx.T C).f n ((StructureCx.T C).f n f)) ⟨(p, q), hpq⟩ = f ⟨(p, q), hpq⟩
  rw [StructureCx.T_apply, StructureCx.T_apply]
  simp only [dualHom_comp, dualHom_units_smul'', dualHom_dualHom, dualHom_eqToHom,
    Linear.units_smul_comp, smul_smul, mul_comm q p, Int.units_mul_self, one_smul,
    Category.assoc, eqToHom_trans, eqToHom_trans_assoc, eqToHom_refl, Category.comp_id,
    Category.id_comp]

end HSP
