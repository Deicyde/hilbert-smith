import HilbertSmithPaper.LTheory.Base.Complexes.StructureComplex

/-!
# The involution T

`T : M(C)_n → M(C)_n`, `(Tf)_r = (-1)^{r(n-r)} (f_{n-r})^*`, is a chain map: `T ∂ = ∂ T`.

Lean: with the pair indexing, `(Tf)_{r,s} = (-1)^{rs} (f_{s,r})^*`, where
`(f_{s,r})^* : (C_s)^* ⟶ (C_r)^{**}` is followed by the identification `(C_r)^{**} = C_r`.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

open DualCat

universe v u

variable {B : Type u} [Category.{v} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B]

namespace StructureCx

private lemma dualHom_units_smul {M N : B} (u : ℤˣ) (f : M ⟶ N) :
    dualHom (u • f) = u • dualHom f := by
  rw [Units.smul_def, Units.smul_def]
  exact (AddMonoidHom.mk' (dualHom (M := M) (N := N)) dualHom_add).map_zsmul (u : ℤ) f

/-- The involution on `M(C)_n`: `(Tf)_{r,s} = (-1)^{rs} (f_{s,r})^*`. -/
def THom (C : ChainComplex B ℤ) (n : ℤ) :
    (∀ x : {x : ℤ × ℤ // x.1 + x.2 = n}, dual (C.X x.1.2) ⟶ C.X x.1.1) →ₗ[ℚ]
      (∀ x : {x : ℤ × ℤ // x.1 + x.2 = n}, dual (C.X x.1.2) ⟶ C.X x.1.1) where
  toFun f x := (x.1.1 * x.1.2).negOnePow •
    (dualHom (f ⟨(x.1.2, x.1.1), by have := x.2; omega⟩) ≫ eqToHom (dual_dual (C.X x.1.1)))
  map_add' f g := by
    funext x
    simp only [Pi.add_apply, dualHom_add, Preadditive.add_comp, smul_add]
  map_smul' c f := by
    funext x
    simp only [Pi.smul_apply, dualHom_smul, Linear.smul_comp, RingHom.id_apply]
    rw [smul_comm]

/-- The involution `T : M(C) ⟶ M(C)`, `(Tf)_r = (-1)^{r(n-r)} (f_{n-r})^*`, a chain map. -/
def T (C : ChainComplex B ℤ) : StructureCx C ⟶ StructureCx C where
  f n := ModuleCat.ofHom (THom C n)
  comm' i j hij := by
    simp only [ComplexShape.down_Rel] at hij
    subst hij
    ext f
    refine funext fun x => ?_
    obtain ⟨⟨p, q⟩, hpq⟩ := x
    subst hpq
    change dHom C (p + q + 1) (p + q) (THom C (p + q + 1) f) ⟨(p, q), rfl⟩ =
      THom C (p + q) (dHom C (p + q + 1) (p + q) f) ⟨(p, q), rfl⟩
    rw [dHom_apply C _ _ _ p q rfl (p + 1) (q + 1) (by omega) (by omega)]
    simp only [THom, LinearMap.coe_mk, AddHom.coe_mk]
    rw [dHom_apply C _ _ f q p (by omega) (q + 1) (p + 1) (by omega) (by omega)]
    simp only [dualHom_add, dualHom_comp, dualHom_units_smul, dualHom_dualHom, Category.assoc,
      Linear.units_smul_comp, Linear.comp_units_smul, Preadditive.add_comp, smul_add, smul_smul,
      eqToHom_trans, eqToHom_refl, Category.comp_id]
    have e1 : ((p + 1) * q).negOnePow = (p * q).negOnePow * q.negOnePow := by
      rw [← Int.negOnePow_add]; congr 1; ring
    have e2 : p.negOnePow * (p * (q + 1)).negOnePow = (p * q).negOnePow := by
      rw [← Int.negOnePow_add, show p + p * (q + 1) = p * q + 2 * p by ring, Int.negOnePow_add,
        Int.negOnePow_two_mul, mul_one]
    rw [e1, e2, add_comm]

/-- The value of `T f` at `(p, q)`: `(-1)^{pq} (f_{q,p})^*`. -/
lemma T_apply (C : ChainComplex B ℤ) (n : ℤ) (f : (StructureCx C).X n) (p q : ℤ)
    (h : p + q = n) :
    ((T C).f n f) ⟨(p, q), h⟩ = (p * q).negOnePow •
      (dualHom (f ⟨(q, p), by omega⟩) ≫ eqToHom (dual_dual (C.X p))) :=
  rfl

end StructureCx

end HSP
