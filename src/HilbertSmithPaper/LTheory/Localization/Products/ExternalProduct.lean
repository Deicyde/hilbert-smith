import Mathlib
import HilbertSmithPaper.LTheory.Localization.Products.Bookkeeping.InclusionProjection
import HilbertSmithPaper.LTheory.Localization.Products.Bookkeeping.InclusionProjectionNe
import HilbertSmithPaper.LTheory.Localization.Products.Bookkeeping.SummandZero
import HilbertSmithPaper.LTheory.Base.Complexes.StructureComplex

/-!
# External product of structures

For a duality pairing `(⊠, κ) : B × E → B''`, complexes `C`, `D` with finitely many nonzero chain
objects, `φ ∈ M(C)_m` and `θ ∈ M(D)_n`, the structure `φ ⊗ θ ∈ M(C ⊗ D)_{m+n}` has, from the
summand `(C_{m-p} ⊠ D_{n-q})^*` of `((C ⊗ D)_{m+n-p-q})^*`, identified with
`C_{m-p}^* ⊠ D_{n-q}^*` through `κ`, to the summand `C_p ⊠ D_q`, the block
`(-1)^{q(p+m)} φ_p ⊠ θ_q`, and zero blocks elsewhere.

Lean: the degree is a parameter `k` with `m + n = k`, so that `φ ⊗ θ` can be compared with
structures of degree `(m - 1) + n` or `m + (n - 1)` without transports. The component at
`(r, s)` (`r + s = k`) is
`∑_{(p,q)} (-1)^{q(p+m)} (ι_{m-p,n-q})^* ≫ κ ≫ (φ_{p,m-p} ⊠ θ_{q,n-q}) ≫ ι_{p,q}`, summed over
the nonzero summands `(p, q)` of `(C ⊗ D)_r`.
-/

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Prod

namespace HSP

open DualCat

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {B : Type u₁} [Category.{v₁} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B]
  {E : Type u₂} [Category.{v₂} E] [Preadditive E] [Linear ℚ E] [HasFiniteBiproducts E]
  [DualCat E]
  {B'' : Type u₃} [Category.{v₃} B''] [Preadditive B''] [Linear ℚ B''] [HasFiniteBiproducts B'']
  [DualCat B'']

/-- **External product of structures.** `φ ⊗ θ ∈ M(C ⊗ D)_k` (`k = m + n`) has the block
`(-1)^{q(p+m)} φ_p ⊠ θ_q` from `(C_{m-p} ⊠ D_{n-q})^* ≅ C_{m-p}^* ⊠ D_{n-q}^*` to `C_p ⊠ D_q`. -/
noncomputable def strProd (P : DualityPairing B E B'') {C : ChainComplex B ℤ}
    {D : ChainComplex E ℤ} (hC : {r | ¬ IsZero (C.X r)}.Finite)
    (hD : {r | ¬ IsZero (D.X r)}.Finite) {m n : ℤ} (φ : (StructureCx C).X m)
    (θ : (StructureCx D).X n) (k : ℤ) (_hk : m + n = k) :
    (StructureCx (cxProd P C D hC hD)).X k := fun x =>
  ∑ y ∈ cxProd.supp hC hD x.1.1, (y.2 * (y.1 + m)).negOnePow •
    (dualHom (cxProd.ι P hC hD (m - y.1) (n - y.2) x.1.2) ≫
      (P.κ (C.X (m - y.1)) (D.X (n - y.2))).hom ≫
      P.tensor.map (φ ⟨(y.1, m - y.1), by ring⟩ ×ₘ θ ⟨(y.2, n - y.2), by ring⟩) ≫
      cxProd.ι P hC hD y.1 y.2 x.1.1)

/-- The block of `φ ⊗ θ` from the dual of the summand `C_c ⊠ D_d` (`c = m - a`, `d = n - b`) to
the summand `C_a ⊠ D_b`: `(-1)^{b(a+m)} κ ≫ (φ_{a,c} ⊠ θ_{b,d})`. -/
lemma strProd_block (P : DualityPairing B E B'') {C : ChainComplex B ℤ}
    {D : ChainComplex E ℤ} (hC : {r | ¬ IsZero (C.X r)}.Finite)
    (hD : {r | ¬ IsZero (D.X r)}.Finite) {m n : ℤ} (φ : (StructureCx C).X m)
    (θ : (StructureCx D).X n) (k : ℤ) (hk : m + n = k) {r s a b c d : ℤ} (hrs : r + s = k)
    (hab : a + b = r) (ha : a + c = m) (hb : b + d = n) :
    dualHom (cxProd.π P hC hD c d s) ≫ strProd P hC hD φ θ k hk ⟨(r, s), hrs⟩ ≫
        cxProd.π P hC hD a b r =
      (b * (a + m)).negOnePow • ((P.κ (C.X c) (D.X d)).hom ≫
        P.tensor.map (φ ⟨(a, c), ha⟩ ×ₘ θ ⟨(b, d), hb⟩)) := by
  obtain rfl : c = m - a := by omega
  obtain rfl : d = n - b := by omega
  change dualHom (cxProd.π P hC hD (m - a) (n - b) s) ≫ (∑ y ∈ cxProd.supp hC hD r, _) ≫ _ = _
  rw [Preadditive.sum_comp, Preadditive.comp_sum]
  by_cases hm : (a, b) ∈ cxProd.supp hC hD r
  · rw [Finset.sum_eq_single (a, b)]
    · simp only [Linear.units_smul_comp, Linear.comp_units_smul, Category.assoc,
        cxProd.ι_π_self P hC hD hab, Category.comp_id]
      rw [← Category.assoc, ← dualHom_comp, cxProd.ι_π_self P hC hD (by omega), dualHom_id,
        Category.id_comp]
    · rintro y _ hy
      rw [Linear.units_smul_comp, Linear.comp_units_smul, Category.assoc, Category.assoc,
        Category.assoc, cxProd.ι_π_of_ne P hC hD (fun h' => hy (Prod.ext h'.1 h'.2)),
        comp_zero, comp_zero, comp_zero, comp_zero, smul_zero]
    · exact fun h' => absurd hm h'
  · exact (cxProd.isZero_of_not_mem_supp P hC hD hab hm).eq_of_tgt _ _

/-- The other blocks of `φ ⊗ θ` vanish. -/
lemma strProd_block_of_ne (P : DualityPairing B E B'') {C : ChainComplex B ℤ}
    {D : ChainComplex E ℤ} (hC : {r | ¬ IsZero (C.X r)}.Finite)
    (hD : {r | ¬ IsZero (D.X r)}.Finite) {m n : ℤ} (φ : (StructureCx C).X m)
    (θ : (StructureCx D).X n) (k : ℤ) (hk : m + n = k) {r s a b c d : ℤ} (hrs : r + s = k)
    (hne : ¬ (a + c = m ∧ b + d = n)) :
    dualHom (cxProd.π P hC hD c d s) ≫ strProd P hC hD φ θ k hk ⟨(r, s), hrs⟩ ≫
        cxProd.π P hC hD a b r = 0 := by
  change dualHom (cxProd.π P hC hD c d s) ≫ (∑ y ∈ cxProd.supp hC hD r, _) ≫ _ = _
  rw [Preadditive.sum_comp, Preadditive.comp_sum]
  refine Finset.sum_eq_zero fun y _ => ?_
  simp only [Linear.units_smul_comp, Linear.comp_units_smul, Category.assoc]
  by_cases hy : y.1 = a ∧ y.2 = b
  · rw [← Category.assoc (dualHom _) (dualHom _), ← dualHom_comp,
      cxProd.ι_π_of_ne P hC hD (fun h' => hne ⟨by omega, by omega⟩), dualHom_zero, zero_comp,
      smul_zero]
  · rw [cxProd.ι_π_of_ne P hC hD hy]
    simp

end HSP
