import HilbertSmithPaper.LTheory.Base.Complexes.Cone
import HilbertSmithPaper.LTheory.Base.Complexes.StructurePush
import HilbertSmithPaper.LTheory.Base.Categories.Sums.DualBinaryBiproducts

/-!
# Pair map

Let `f : C ⟶ D` be a chain map, `m + 1 = n`, `φ ∈ M(C)_m` with `∂φ = 0`, and `δφ ∈ M(D)_n` with
`∂δφ = f_% φ`. Then `ψ_r = (δφ_r, (-1)^r φ_{r-1} f^*_{n-r}) : D^*_{n-r} ⟶ 𝒞(f)_r` is a chain
map `ψ : D^{n-*} ⟶ 𝒞(f)`.

The two dimensions `m` and `n` are separate variables with `m + 1 = n` (rather than `n - 1`),
so that pairs whose boundary has a given dimension need no transport.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

open DualCat

universe v u

variable {B : Type u} [Category.{v} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B]

/-- The pair map `ψ : D^{n-*} ⟶ 𝒞(f)`,
`ψ_r = (δφ_{r,n-r}, (-1)^r φ_{r-1,n-r} ∘ (f_{n-r})^*) : (D_{n-r})^* ⟶ D_r ⊞ C_{r-1}`. -/
noncomputable def pairMap {C D : ChainComplex B ℤ} (f : C ⟶ D) {m n : ℤ} (hmn : m + 1 = n)
    (δφ : (StructureCx D).X n) (φ : (StructureCx C).X m)
    (hφ : (StructureCx C).d m (m - 1) φ = 0)
    (hδφ : (StructureCx D).d n m δφ = (StructureCx.push f).f m φ) : dualCx D n ⟶ cone f where
  f r := biprod.lift (δφ ⟨(r, n - r), by simp⟩)
    (r.negOnePow • (dualHom (f.f (n - r)) ≫ φ ⟨(r - 1, n - r), by omega⟩))
  comm' i j hij := by
    simp only [ComplexShape.down_Rel] at hij
    obtain rfl : j = i - 1 := by omega
    have h1 := congrFun hφ ⟨(i - 1 - 1, n - i), by omega⟩
    rw [StructureCx.d_apply C m (m - 1) φ (i - 1 - 1) (n - i) _ (i - 1) (n - (i - 1)) (by omega)
      (by omega)] at h1
    have h2 := congrFun hδφ ⟨(i - 1, n - i), by omega⟩
    rw [StructureCx.d_apply D n m δφ (i - 1) (n - i) _ i (n - (i - 1)) (by omega)
      (by omega), StructureCx.push_apply] at h2
    change _ = (0 : dual (C.X (n - i)) ⟶ C.X (i - 1 - 1)) at h1
    have hs : (i - 1).negOnePow = -i.negOnePow := by
      rw [Int.negOnePow_sub, Int.negOnePow_one, mul_neg_one]
    have hs2 : (i - 1 - 1).negOnePow = i.negOnePow := by
      rw [Int.negOnePow_sub, hs, Int.negOnePow_one, neg_mul_neg, mul_one]
    rw [hs2] at h1
    rw [hs] at h2
    change _ ≫ cone.d f i (i - 1) = _
    simp only [cone.d, dite_true]
    apply biprod.hom_ext
    · simp only [biprod.lift_fst_assoc, biprod.lift_snd_assoc, Linear.units_smul_comp,
        Category.assoc, Preadditive.comp_add, Linear.comp_units_smul, biprod.lift_fst,
        HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Category.comp_id]
      rw [← h2, hs, smul_smul, neg_mul, Int.units_mul_self]
      simp only [Units.neg_smul, one_smul, smul_add, neg_neg]
      abel
    · simp only [biprod.lift_snd_assoc, Linear.units_smul_comp, Category.assoc,
        Linear.comp_units_smul, biprod.lift_snd]
      rw [eq_neg_of_add_eq_zero_left h1, hs, Preadditive.comp_neg, Linear.comp_units_smul,
        Units.neg_smul, smul_neg, ← Category.assoc (dualHom (D.d _ _)), ← dualHom_comp, f.comm,
        dualHom_comp, Category.assoc, smul_neg]

end HSP
