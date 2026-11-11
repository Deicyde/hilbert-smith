import HilbertSmithPaper.LTheory.Base.Complexes.StructureComplex

/-!
# Pushforward of structures

A chain map `g : C ⟶ D` gives a chain map `g_% : M(C) ⟶ M(D)`,
`(g_% f)_r = g_r f_r (g_{n-r})^*`; in pair indices `(g_% f)_{r,s} = g_r f_{r,s} (g_s)^*`.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

open DualCat

universe v u

variable {B : Type u} [Category.{v} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B]

namespace StructureCx

/-- The pushforward on `M(C)_n`: `(g_% f)_{r,s} = g_r f_{r,s} (g_s)^*`. -/
def pushHom {C D : ChainComplex B ℤ} (g : C ⟶ D) (n : ℤ) :
    (∀ x : {x : ℤ × ℤ // x.1 + x.2 = n}, dual (C.X x.1.2) ⟶ C.X x.1.1) →ₗ[ℚ]
      (∀ x : {x : ℤ × ℤ // x.1 + x.2 = n}, dual (D.X x.1.2) ⟶ D.X x.1.1) where
  toFun f x := dualHom (g.f x.1.2) ≫ f x ≫ g.f x.1.1
  map_add' f g := by
    funext x
    simp only [Pi.add_apply, Preadditive.add_comp, Preadditive.comp_add]
  map_smul' c f := by
    funext x
    simp only [Pi.smul_apply, Linear.smul_comp, Linear.comp_smul, RingHom.id_apply]

/-- The pushforward `g_% : M(C) ⟶ M(D)` along a chain map `g : C ⟶ D`,
`(g_% f)_r = g_r f_r (g_{n-r})^*`. -/
def push {C D : ChainComplex B ℤ} (g : C ⟶ D) : StructureCx C ⟶ StructureCx D where
  f n := ModuleCat.ofHom (pushHom g n)
  comm' i j hij := by
    simp only [ComplexShape.down_Rel] at hij
    subst hij
    ext f ⟨⟨p, q⟩, hpq⟩
    subst hpq
    change dHom D (p + q + 1) (p + q) (pushHom g (p + q + 1) f) ⟨(p, q), rfl⟩ =
      pushHom g (p + q) (dHom C (p + q + 1) (p + q) f) ⟨(p, q), rfl⟩
    rw [dHom_apply D _ _ _ p q rfl (p + 1) (q + 1) (by omega) (by omega)]
    simp only [pushHom, LinearMap.coe_mk, AddHom.coe_mk]
    rw [dHom_apply C _ _ f p q rfl (p + 1) (q + 1) (by omega) (by omega)]
    simp only [Category.assoc, Preadditive.add_comp, Preadditive.comp_add, Linear.units_smul_comp,
      Linear.comp_units_smul, g.comm]
    rw [← Category.assoc (dualHom (D.d (q + 1) q)), ← dualHom_comp, g.comm, dualHom_comp,
      Category.assoc]

/-- The value of `g_% f` at `(p, q)`: `(g_q)^* ≫ f_{p,q} ≫ g_p`. -/
lemma push_apply {C D : ChainComplex B ℤ} (g : C ⟶ D) (n : ℤ) (f : (StructureCx C).X n)
    (p q : ℤ) (h : p + q = n) :
    ((push g).f n f) ⟨(p, q), h⟩ = dualHom (g.f q) ≫ f ⟨(p, q), h⟩ ≫ g.f p :=
  rfl

/-- `g_%` commutes with `∂`, applied to an element. -/
lemma d_push_apply {C D : ChainComplex B ℤ} (g : C ⟶ D) (n m : ℤ) (x : (StructureCx C).X n) :
    (StructureCx D).d n m ((push g).f n x) = (push g).f m ((StructureCx C).d n m x) := by
  have := ConcreteCategory.congr_hom ((push g).comm n m) x
  simpa using this

end StructureCx

end HSP
