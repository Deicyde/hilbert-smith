import Mathlib
import HilbertSmithPaper.ChainModels.Grid.Tensor.StructureProducts.DualProdBlocks
import HilbertSmithPaper.ChainModels.Grid.Tensor.StructureProducts.StrProdBlocks
import HilbertSmithPaper.ChainModels.Grid.Tensor.StructureProducts.TensorHomTransportBlocks
import HilbertSmithPaper.ChainModels.Grid.Tensor.StructureProducts.ZeroDimComp
import HilbertSmithPaper.ChainModels.Grid.Tensor.BlockComp
import HilbertSmithPaper.ChainModels.Grid.Tensor.BlockExt
import HilbertSmithPaper.ChainModels.Grid.Tensor.KronComposite
import HilbertSmithPaper.ChainModels.Grid.Tensor.KronZero

/-!
# A product of structures after a product of duality maps

`(φ ⊗ θ) ∘ Ξ^{-1}(f ⊗ g) = (φ f) ⊗ (θ g)`, a tensor of maps of degree `0`, when `C` and `E` vanish in negative degrees.

## Proof

Blockwise: the only intermediate dual summand is `m - a`, the two signs are equal, and when that summand is out of range the factor `C_{m-a}` or `E_{m'-r+a}` vanishes.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Kronecker

namespace HSP.ChainModels

open FreeQ DualCat

variable {C E : ChainComplex FreeQ ℤ}

variable (hE : ∀ q < 0, (E.X q).dim = 0)

private lemma kron_through {X₀ X₁ X₂ X₂' Y₀ Y₁ Y₂ Y₂' M : FreeQ} (x : X₀ ⟶ X₁) (y : Y₀ ⟶ Y₁)
    (u : X₁ ⟶ X₂) (v : Y₁ ⟶ Y₂) (hX : X₂ = X₂') (hY : Y₂ = Y₂')
    (e1 : (⟨X₁.dim * Y₁.dim⟩ : FreeQ) = M) (e2 : M = ⟨X₁.dim * Y₁.dim⟩)
    (e3 : (⟨X₂'.dim * Y₂'.dim⟩ : FreeQ) = ⟨X₂.dim * Y₂.dim⟩) :
    basedKron x y ≫ eqToHom e1 ≫ eqToHom e2 ≫ basedKron u v =
      basedKron (x ≫ u ≫ eqToHom hX) (y ≫ v ≫ eqToHom hY) ≫ eqToHom e3 := by
  subst hX hY
  simp only [eqToHom_trans_assoc, eqToHom_refl, Category.comp_id, Category.id_comp]
  rw [basedKron_comp_basedKron]

theorem basedDualProd_comp_basedStrProd (hC : ∀ q < 0, (C.X q).dim = 0) (m m' k : ℤ)
    (hk : m + m' = k) (f : ∀ r, C.X r ⟶ dual (C.X (m - r))) (g : ∀ r, E.X r ⟶ dual (E.X (m' - r)))
    (φ : (StructureCx C).X m) (θ : (StructureCx E).X m') (r : ℤ) :
    basedDualProd C E hE m m' k hk f g r ≫ basedStrProd C E hE m m' k hk φ θ ⟨(r, k - r), by ring⟩ =
      basedTensorHom hE hE 0 0
          (fun a => f a ≫ φ ⟨(a, m - a), by ring⟩ ≫ eqToHom (congrArg C.X (add_zero a).symm))
          (fun c => g c ≫ θ ⟨(c, m' - c), by ring⟩ ≫ eqToHom (congrArg E.X (add_zero c).symm)) r ≫
        eqToHom (congrArg (basedComplexTensor C E hE).X (by ring)) := by
  have hrk : r + (k - r) = k := by ring
  refine block_ext fun a p => ?_
  refine (block_comp _ _ a p).trans ?_
  refine Eq.trans (Finset.sum_congr rfl fun q _ => congrArg₂ (· ≫ ·)
    (blockInc_comp_basedDualProd_comp_blockProj hE m m' k hk f g r a q)
    (blockInc_comp_basedStrProd_comp_blockProj hE m m' k hk φ θ r (k - r) hrk q p)) ?_
  refine Eq.trans ?_
    (blockInc_comp_basedTensorHom_comp_eqToHom_comp_blockProj hE hE 0 0 _ _ r r (by ring) a p).symm
  by_cases hp : ((p : ℕ) : ℤ) = (a : ℕ) + 0
  · have hpa : p = a := Fin.ext (by omega)
    subst hpa
    have hp' : (((p : ℕ) : ℤ) = (p : ℕ) + 0) = True := eq_true (by ring)
    simp only [hp', ↓reduceDIte, zero_mul, Int.negOnePow_zero, one_smul]
    by_cases hin : 0 ≤ m - (p : ℕ) ∧ m - (p : ℕ) ≤ ((k - r).toNat : ℤ)
    · rw [Finset.sum_eq_single (⟨(m - (p : ℕ)).toNat, by omega⟩ : Fin ((k - r).toNat + 1))]
      · have hq : ((((⟨(m - (p : ℕ)).toNat, by omega⟩ : Fin ((k - r).toNat + 1)) : ℕ) : ℤ) =
            m - (p : ℕ)) = True := eq_true (by simp only; omega)
        simp only [hq, ↓reduceDIte, Linear.units_smul_comp, Linear.comp_units_smul, smul_smul,
          Int.units_mul_self, one_smul, Category.assoc]
        exact kron_through _ _ _ _ _ _ _ _ _
      · intro q _ hq
        have hq' : ¬ (((q : ℕ) : ℤ) = m - (p : ℕ)) := fun h' => hq (Fin.ext (by simp only; omega))
        simp only [hq', ↓reduceDIte, zero_comp]
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [Finset.sum_eq_zero]
      · symm
        rw [not_and_or] at hin
        rcases hin with hin | hin
        · rw [comp_eq_zero_of_dim (f _) _ (by
              change (C.X (m - ((p : ℕ) : ℤ))).dim = 0; exact hC _ (by omega)),
            basedKron_eq_zero (Or.inl rfl), zero_comp]
        · rw [comp_eq_zero_of_dim (g _) _ (by
              change (E.X (m' - (r - ((p : ℕ) : ℤ)))).dim = 0; exact hE _ (by omega)),
            basedKron_eq_zero (Or.inr rfl), zero_comp]
      · intro q _
        have hq' : ¬ (((q : ℕ) : ℤ) = m - (p : ℕ)) := fun h' => hin ⟨by omega, by omega⟩
        simp only [hq', ↓reduceDIte, zero_comp]
  · have hp' : ¬ (((p : ℕ) : ℤ) = (a : ℕ) + 0) := hp
    simp only [hp', ↓reduceDIte]
    refine Finset.sum_eq_zero fun q _ => ?_
    by_cases hq : ((q : ℕ) : ℤ) = m - (a : ℕ)
    · have hq' : ¬ (((q : ℕ) : ℤ) = m - (p : ℕ)) := by omega
      simp only [hq', ↓reduceDIte, comp_zero]
    · simp only [hq, ↓reduceDIte, zero_comp]

end HSP.ChainModels
