import HilbertSmithPaper.LTheory.Base.Complexes.StructureComplex

/-!
# Duality map of a cycle

For `φ ∈ M(C)_n` with `∂φ = 0`, the components `φ_r = φ_{r,n-r} : (C_{n-r})^* ⟶ C_r` form a
chain map `φ_♮ : C^{n-*} ⟶ C`. The chain map condition `d φ_r = (-1)^r φ_{r-1} d^*` is
`(∂φ)_{r-1} = 0`.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

open DualCat

universe v u

variable {B : Type u} [Category.{v} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B]

/-- The duality map `φ_♮ : C^{n-*} ⟶ C` of a cycle `φ ∈ M(C)_n`, `(φ_♮)_r = φ_{r,n-r}`. -/
@[simps]
def StructureCx.toHom {C : ChainComplex B ℤ} {n : ℤ} (φ : (StructureCx C).X n)
    (hφ : (StructureCx C).d n (n - 1) φ = 0) : dualCx C n ⟶ C where
  f r := φ ⟨(r, n - r), by simp⟩
  comm' i j hij := by
    simp only [ComplexShape.down_Rel] at hij
    subst hij
    have h := congrFun hφ ⟨(j, n - (j + 1)), by omega⟩
    rw [StructureCx.d_apply C n (n - 1) φ j (n - (j + 1)) _ (j + 1) (n - j) (by omega)
      (by omega)] at h
    change φ ⟨(j + 1, n - (j + 1)), _⟩ ≫ C.d (j + 1) j =
      ((j + 1).negOnePow • dualHom (C.d (n - j) (n - (j + 1)))) ≫ φ ⟨(j, n - j), _⟩
    rw [Linear.units_smul_comp, eq_comm, Int.negOnePow_succ, Units.neg_smul, neg_eq_iff_add_eq_zero]
    exact (add_comm _ _).trans h

end HSP
