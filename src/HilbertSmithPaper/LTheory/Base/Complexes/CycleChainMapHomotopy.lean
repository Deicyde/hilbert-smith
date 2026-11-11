import Mathlib
import HilbertSmithPaper.LTheory.Base.Complexes.CycleChainMap

/-!
# Homologous cycles give homotopic maps

If `φ, φ' ∈ M(C)_n` are cycles and `φ - φ' = ∂X` for some `X ∈ M(C)_{n+1}`, then the duality maps
`φ_♮, φ'_♮ : C^{n-*} ⟶ C` are chain homotopic, with the homotopy `H_r = X_{r+1,n-r}`. The
identity `(∂X)_{r,n-r} = d X_{r+1,n-r} + (-1)^r X_{r,n-r+1} d^*` is the homotopy equation, the
differential of `C^{n-*}` being `(-1)^r d^*`.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

open DualCat

universe v u

variable {B : Type u} [Category.{v} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B]

/-- **Homologous cycles give homotopic maps.** If `φ - φ' = ∂X`, then `φ_♮ ≃ φ'_♮`, with the
homotopy `H_r = X_{r+1,n-r}`. -/
theorem StructureCx.toHom_homotopy {C : ChainComplex B ℤ} {n : ℤ} (φ φ' : (StructureCx C).X n)
    (hφ : (StructureCx C).d n (n - 1) φ = 0) (hφ' : (StructureCx C).d n (n - 1) φ' = 0)
    (X : (StructureCx C).X (n + 1)) (h : (StructureCx C).d (n + 1) n X = φ - φ') :
    Nonempty (Homotopy (StructureCx.toHom φ hφ) (StructureCx.toHom φ' hφ')) := by
  refine ⟨{ hom := fun i j => if hj : j = i + 1 then X ⟨(j, n - i), by omega⟩ else 0
            zero := fun i j hij => dite_eq_right (by simp only [ComplexShape.down_Rel] at hij; omega)
            comm := fun i => ?_ }⟩
  have hX := congrFun h ⟨(i, n - i), by omega⟩
  rw [StructureCx.d_apply C (n + 1) n X i (n - i) _ (i + 1) (n - (i - 1)) (by omega)
    (by omega)] at hX
  rw [dNext_eq _ (show (ComplexShape.down ℤ).Rel i (i - 1) by simp),
    prevD_eq _ (show (ComplexShape.down ℤ).Rel (i + 1) i by simp),
    dite_eq_left (show i = i - 1 + 1 by omega), dite_eq_left rfl, StructureCx.toHom_f,
    StructureCx.toHom_f]
  change φ ⟨(i, n - i), _⟩ = (i.negOnePow • dualHom (C.d (n - (i - 1)) (n - i))) ≫
      X ⟨(i, n - (i - 1)), _⟩ + X ⟨(i + 1, n - i), _⟩ ≫ C.d (i + 1) i + φ' ⟨(i, n - i), _⟩
  change _ = φ ⟨(i, n - i), _⟩ - φ' ⟨(i, n - i), _⟩ at hX
  rw [Linear.units_smul_comp, add_comm (i.negOnePow • _), hX, sub_add_cancel]

end HSP
