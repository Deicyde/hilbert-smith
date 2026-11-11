import HilbertSmithPaper.LTheory.Base.Complexes.DualComplex

/-!
# Structure complex

For a complex `C` in a duality category, `M(C)_n = ∏_{r+s=n} Hom(C_s^*, C_r)`, indexed by the
pairs `(r, s)` with `r + s = n`, with differential
`(∂f)_{r,s} = d f_{r+1,s} + (-1)^r f_{r,s+1} d^*`. Then `∂² = 0`, so `M(C)` is a chain complex of
ℚ-vector spaces.

Lean: an element of `M(C)_n` is a function on the subtype `{x : ℤ × ℤ // x.1 + x.2 = n}`, whose
value at `⟨(r, s), _⟩` is a morphism `(C_s)^* ⟶ C_r`. The pair indexing avoids transports along
`n - (n - r) = r`. The differential `∂ : M(C)_n ⟶ M(C)_m` is written for all `n m` as
`(∂f)_{r,s} = f_{n-s,s} ≫ d_{n-s,r} + (-1)^r d^*_{n-r,s} ≫ f_{r,n-r}`, which is the formula above
when `m + 1 = n` and zero otherwise (Mathlib's `HomComplex` uses the same device).
`StructureCx.d_apply` evaluates it with any indices.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

open DualCat

universe v u

variable {B : Type u} [Category.{v} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B]

namespace StructureCx

/-- The differential `∂ : M(C)_n → M(C)_m`,
`(∂f)_{r,s} = f_{n-s,s} ≫ d_{n-s,r} + (-1)^r d^*_{n-r,s} ≫ f_{r,n-r}`. -/
def dHom (C : ChainComplex B ℤ) (n m : ℤ) :
    (∀ x : {x : ℤ × ℤ // x.1 + x.2 = n}, dual (C.X x.1.2) ⟶ C.X x.1.1) →ₗ[ℚ]
      (∀ x : {x : ℤ × ℤ // x.1 + x.2 = m}, dual (C.X x.1.2) ⟶ C.X x.1.1) where
  toFun f x := f ⟨(n - x.1.2, x.1.2), by simp⟩ ≫ C.d (n - x.1.2) x.1.1 +
    x.1.1.negOnePow • (dualHom (C.d (n - x.1.1) x.1.2) ≫ f ⟨(x.1.1, n - x.1.1), by simp⟩)
  map_add' f g := by
    funext x
    simp only [Pi.add_apply, Preadditive.add_comp, Preadditive.comp_add, smul_add]
    abel
  map_smul' c f := by
    funext x
    simp only [Pi.smul_apply, Linear.smul_comp, Linear.comp_smul, RingHom.id_apply, smul_add]
    rw [smul_comm]

lemma dHom_apply (C : ChainComplex B ℤ) (n m : ℤ)
    (f : ∀ x : {x : ℤ × ℤ // x.1 + x.2 = n}, dual (C.X x.1.2) ⟶ C.X x.1.1)
    (p q : ℤ) (h : p + q = m) (p' q' : ℤ) (hp' : p' + q = n) (hq' : p + q' = n) :
    dHom C n m f ⟨(p, q), h⟩ = f ⟨(p', q), hp'⟩ ≫ C.d p' p +
      p.negOnePow • (dualHom (C.d q' q) ≫ f ⟨(p, q'), hq'⟩) := by
  obtain rfl : p' = n - q := by omega
  obtain rfl : q' = n - p := by omega
  rfl

end StructureCx

/-- The structure complex `M(C)`: `M(C)_n = ∏_{r+s=n} Hom((C_s)^*, C_r)` with
`(∂f)_{r,s} = d f_{r+1,s} + (-1)^r f_{r,s+1} d^*`; a chain complex of ℚ-vector spaces. -/
abbrev StructureCx (C : ChainComplex B ℤ) : ChainComplex (ModuleCat.{v} ℚ) ℤ where
  X n := ModuleCat.of ℚ (∀ x : {x : ℤ × ℤ // x.1 + x.2 = n}, dual (C.X x.1.2) ⟶ C.X x.1.1)
  d n m := ModuleCat.ofHom (StructureCx.dHom C n m)
  shape n m h := by
    simp only [ComplexShape.down_Rel] at h
    ext f x
    obtain ⟨⟨p, q⟩, hpq⟩ := x
    simp only [ModuleCat.hom_ofHom, ModuleCat.hom_zero, LinearMap.zero_apply]
    rw [StructureCx.dHom_apply C n m f p q hpq (n - q) (n - p) (by omega) (by omega),
      C.shape, C.shape, dualHom_zero]
    · simp only [comp_zero, zero_comp, smul_zero, add_zero]; rfl
    all_goals simp only [ComplexShape.down_Rel]; omega
  d_comp_d' i j k hij hjk := by
    simp only [ComplexShape.down_Rel] at hij hjk
    subst hij hjk
    ext f x
    obtain ⟨⟨p, q⟩, hpq⟩ := x
    subst hpq
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
      ModuleCat.hom_zero, LinearMap.zero_apply]
    rw [StructureCx.dHom_apply C _ _ _ p q rfl (p + 1) (q + 1) (by omega) (by omega),
      StructureCx.dHom_apply C _ _ f (p + 1) q (by omega) (p + 2) (q + 1) (by omega) (by omega),
      StructureCx.dHom_apply C _ _ f p (q + 1) (by omega) (p + 1) (q + 2) (by omega) (by omega)]
    simp only [Preadditive.add_comp, Preadditive.comp_add, Linear.units_smul_comp,
      Linear.comp_units_smul, Category.assoc, C.d_comp_d]
    have hdd : ∀ {Z : B} (g : dual (C.X (q + 2)) ⟶ Z),
        dualHom (C.d (q + 1) q) ≫ dualHom (C.d (q + 2) (q + 1)) ≫ g = 0 := by
      intro Z g
      rw [← Category.assoc, ← dualHom_comp, C.d_comp_d, dualHom_zero, zero_comp]
    simp only [hdd, comp_zero, smul_zero, add_zero, Int.negOnePow_succ, Units.neg_smul]
    rw [zero_add, neg_add_cancel]
    rfl

namespace StructureCx

/-- The value of `∂ f` at `(p, q)`, with any indices `p' = n - q` and `q' = n - p`:
`(∂f)_{p,q} = f_{p',q} ≫ d_{p',p} + (-1)^p d^*_{q',q} ≫ f_{p,q'}`. -/
lemma d_apply (C : ChainComplex B ℤ) (n m : ℤ) (f : (StructureCx C).X n)
    (p q : ℤ) (h : p + q = m) (p' q' : ℤ) (hp' : p' + q = n) (hq' : p + q' = n) :
    ((StructureCx C).d n m f) ⟨(p, q), h⟩ = f ⟨(p', q), hp'⟩ ≫ C.d p' p +
      p.negOnePow • (dualHom (C.d q' q) ≫ f ⟨(p, q'), hq'⟩) :=
  dHom_apply C n m f p q h p' q' hp' hq'

end StructureCx

end HSP
