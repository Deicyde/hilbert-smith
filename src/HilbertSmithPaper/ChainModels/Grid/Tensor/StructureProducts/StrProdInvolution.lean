import Mathlib
import HilbertSmithPaper.ChainModels.Grid.Tensor.StructureProducts.StrProdBlocks
import HilbertSmithPaper.ChainModels.Grid.Tensor.StructureProducts.BlockDual
import HilbertSmithPaper.ChainModels.Grid.Tensor.KronDual
import HilbertSmithPaper.ChainModels.Grid.Tensor.KronSmulLeft
import HilbertSmithPaper.ChainModels.Grid.Tensor.KronSmulRight
import HilbertSmithPaper.ChainModels.Grid.Tensor.BlockExt
import HilbertSmithPaper.LTheory.Base.Complexes.StructureInvolution

/-!
# Products of structures commute with the involution

`T(φ ⊗ θ) = Tφ ⊗ Tθ`.

## Proof

Blockwise: the block of `T(φ ⊗ θ)` is the transpose of a block of `φ ⊗ θ`, and the transpose of a Kronecker product is the Kronecker product of the transposes; the signs agree because `rs + (s-a)(a+m) ≡ (r-p)(p+m) + p(m-p) + (r-p)(m'-r+p) (mod 2)` when `a = m - p`.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Kronecker

namespace HSP.ChainModels

open FreeQ DualCat

variable {C E : ChainComplex FreeQ ℤ}

variable (hE : ∀ q < 0, (E.X q).dim = 0)

private lemma eqToHom_dual_dual (X : FreeQ) : eqToHom (dual_dual X) = 𝟙 X := rfl

private lemma comp_eqToHom_dual_dual {X Y : FreeQ} (f : X ⟶ dual (dual Y)) :
    f ≫ eqToHom (dual_dual Y) = f :=
  Category.comp_id f

private lemma kron_dual_transport {m m' : ℤ} (φ : (StructureCx C).X m) (θ : (StructureCx E).X m')
    {i i' j j' u u' v v' : ℤ} (hi : i = i') (hj : j = j') (hu : u = u') (hv : v = v')
    (hij : i + j = m) (hij' : i' + j' = m) (huv : u + v = m') (huv' : u' + v' = m')
    (h0 : (⟨(dual (C.X i)).dim * (dual (E.X u)).dim⟩ : FreeQ) =
      ⟨(dual (C.X i')).dim * (dual (E.X u')).dim⟩)
    (h1 : (⟨(dual (dual (C.X j))).dim * (dual (dual (E.X v))).dim⟩ : FreeQ) =
      ⟨(dual (dual (C.X j'))).dim * (dual (dual (E.X v'))).dim⟩) :
    basedKron (dualHom (φ ⟨(i, j), hij⟩)) (dualHom (θ ⟨(u, v), huv⟩)) ≫ eqToHom h1 =
      eqToHom h0 ≫ basedKron (dualHom (φ ⟨(i', j'), hij'⟩)) (dualHom (θ ⟨(u', v'), huv'⟩)) := by
  subst hi hj hu hv; simp

private lemma blk_T {m m' : ℕ} (d : Fin m → ℕ) (d' : Fin m' → ℕ)
    (X : (⟨∑ i, d i⟩ : FreeQ) ⟶ ⟨∑ i, d' i⟩) (u : ℤˣ) (p : Fin m) (q : Fin m') :
    blockInc d' q ≫ (u • dualHom X ≫ eqToHom (dual_dual _)) ≫ blockProj d p =
      u • dualHom (blockInc d p ≫ X ≫ blockProj d' q) := by
  rw [Linear.units_smul_comp, Linear.comp_units_smul, comp_eqToHom_dual_dual]
  exact congrArg (u • ·) (blockInc_comp_dualHom_comp_blockProj d d' X p q)

theorem basedStrProd_T (m m' k : ℤ) (hk : m + m' = k) (φ : (StructureCx C).X m)
    (θ : (StructureCx E).X m') :
    (StructureCx.T (basedComplexTensor C E hE)).f k (basedStrProd C E hE m m' k hk φ θ) =
      basedStrProd C E hE m m' k hk ((StructureCx.T C).f m φ) ((StructureCx.T E).f m' θ) := by
  have hdu : ∀ {X Y : FreeQ} (u : ℤˣ) (f : X ⟶ Y), dualHom (u • f) = u • dualHom f :=
    fun {X Y} u f => by
      rw [Units.smul_def, Units.smul_def]
      exact (AddMonoidHom.mk' (dualHom (M := X) (N := Y)) dualHom_add).map_zsmul (u : ℤ) f
  funext x
  obtain ⟨⟨r, s⟩, h⟩ := x
  dsimp only at h ⊢
  refine block_ext fun a p => ?_
  have hL : blockInc (tensorSummandDim C E s) a ≫
      ((StructureCx.T (basedComplexTensor C E hE)).f k (basedStrProd C E hE m m' k hk φ θ))
        ⟨(r, s), h⟩ ≫ blockProj (tensorSummandDim C E r) p =
      (r * s).negOnePow • dualHom (blockInc (tensorSummandDim C E r) p ≫
        basedStrProd C E hE m m' k hk φ θ ⟨(s, r), by omega⟩ ≫
          blockProj (tensorSummandDim C E s) a) := by
    rw [StructureCx.T_apply]
    exact blk_T _ _ _ _ p a
  refine hL.trans (Eq.trans ?_
    (blockInc_comp_basedStrProd_comp_blockProj hE m m' k hk _ _ r s h a p).symm)
  rw [blockInc_comp_basedStrProd_comp_blockProj]
  by_cases h' : ((a : ℕ) : ℤ) = m - (p : ℕ)
  · have c1 : (((p : ℕ) : ℤ) = m - (a : ℕ)) = True := eq_true (by omega)
    have c2 : (((a : ℕ) : ℤ) = m - (p : ℕ)) = True := eq_true h'
    simp only [c1, c2, ↓reduceDIte, hdu, dualHom_comp, dualHom_basedKron,
      dualHom_eqToHom, smul_smul]
    rw [StructureCx.T_apply, StructureCx.T_apply, comp_eqToHom_dual_dual, comp_eqToHom_dual_dual,
      basedKron_units_smul_left, basedKron_units_smul_right, Linear.comp_units_smul,
      Linear.comp_units_smul, smul_smul, smul_smul]
    congr 1
    · rw [← Int.negOnePow_add, ← Int.negOnePow_add, ← Int.negOnePow_add, Int.negOnePow_eq_iff]
      have hs : s = m + m' - r := by omega
      rw [show ((a : ℕ) : ℤ) = m - (p : ℕ) from h']
      exact ⟨m * m' - m * r + m * (p : ℕ) - r * (p : ℕ) + (p : ℕ) * (p : ℕ),
        by linear_combination (r + 2 * m - (p : ℤ)) * hs⟩
    · exact kron_dual_transport φ θ (by omega) (by omega) (by dsimp only; omega) (by omega)
        _ _ _ _ _ _
  · have h'' : ¬ ((p : ℕ) : ℤ) = m - (a : ℕ) := by omega
    simp only [h', h'', ↓reduceDIte, dualHom_zero, smul_zero]

end HSP.ChainModels
