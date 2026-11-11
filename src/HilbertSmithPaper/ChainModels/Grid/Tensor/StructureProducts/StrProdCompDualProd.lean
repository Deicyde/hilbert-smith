import Mathlib
import HilbertSmithPaper.ChainModels.Grid.Tensor.StructureProducts.DualProdBlocks
import HilbertSmithPaper.ChainModels.Grid.Tensor.StructureProducts.StrProdBlocks
import HilbertSmithPaper.ChainModels.Grid.Tensor.StructureProducts.DualTensorHomBlocks
import HilbertSmithPaper.ChainModels.Grid.Tensor.StructureProducts.ZeroDimComp
import HilbertSmithPaper.ChainModels.Grid.Tensor.BlockComp
import HilbertSmithPaper.ChainModels.Grid.Tensor.BlockExt
import HilbertSmithPaper.ChainModels.Grid.Tensor.KronComposite
import HilbertSmithPaper.ChainModels.Grid.Tensor.KronTransport
import HilbertSmithPaper.ChainModels.Grid.Tensor.KronZero

/-!
# A product of duality maps after a product of structures

`Ξ^{-1}(f ⊗ g) ∘ (φ ⊗ θ) = Ξ^{-1}((f φ) ⊗ (g θ))Ξ`, a dual tensor of maps of degree `0`, when `C` and `E` vanish in negative degrees.

## Proof

Blockwise: the only intermediate summand is `m - a`, the two signs are equal, the sign of the dual tensor is even, and when that summand is out of range the factor `C_{m-a}` or `E_{r-m+a}` vanishes.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Kronecker

namespace HSP.ChainModels

open FreeQ DualCat

variable {C E : ChainComplex FreeQ ℤ}

variable (hE : ∀ q < 0, (E.X q).dim = 0)

private lemma kron_through' {m m' : ℤ} (φ : (StructureCx C).X m) (θ : (StructureCx E).X m')
    (f : ∀ r, C.X r ⟶ dual (C.X (m - r))) (g : ∀ r, E.X r ⟶ dual (E.X (m' - r)))
    {i i' j j' u u' v v' : ℤ} (hi : i = i') (hj : j = j') (hu : u = u') (hv : v = v')
    (hij : i + j = m) (hij' : i' + j' = m) (huv : u + v = m') (huv' : u' + v' = m')
    {W Z : FreeQ} (e0 : W = ⟨(dual (C.X j)).dim * (dual (E.X v)).dim⟩)
    (e2 : W = ⟨(dual (C.X j')).dim * (dual (E.X v')).dim⟩)
    (e1 : (⟨(dual (C.X (m - i))).dim * (dual (E.X (m' - u))).dim⟩ : FreeQ) = Z)
    (hX : dual (C.X (m - i')) = dual (C.X (m - (i' + 0))))
    (hY : dual (E.X (m' - u')) = dual (E.X (m' - (u' + 0))))
    (e3 : (⟨(dual (C.X (m - (i' + 0)))).dim * (dual (E.X (m' - (u' + 0)))).dim⟩ : FreeQ) = Z) :
    eqToHom e0 ≫ basedKron (φ ⟨(i, j), hij⟩) (θ ⟨(u, v), huv⟩) ≫ basedKron (f i) (g u) ≫
        eqToHom e1 =
      eqToHom e2 ≫ basedKron (φ ⟨(i', j'), hij'⟩ ≫ f i' ≫ eqToHom hX)
        (θ ⟨(u', v'), huv'⟩ ≫ g u' ≫ eqToHom hY) ≫ eqToHom e3 := by
  subst hi hj hu hv e0
  simp only [eqToHom_refl, Category.id_comp]
  rw [← basedKron_comp_basedKron, ← basedKron_comp_basedKron, basedKron_eqToHom, Category.assoc,
    Category.assoc, eqToHom_trans]

theorem basedStrProd_comp_basedDualProd (hC : ∀ q < 0, (C.X q).dim = 0) (m m' k : ℤ)
    (hk : m + m' = k) (f : ∀ r, C.X r ⟶ dual (C.X (m - r))) (g : ∀ r, E.X r ⟶ dual (E.X (m' - r)))
    (φ : (StructureCx C).X m) (θ : (StructureCx E).X m') (r : ℤ) :
    basedStrProd C E hE m m' k hk φ θ ⟨(r, k - r), by ring⟩ ≫ basedDualProd C E hE m m' k hk f g r =
      basedDualTensorHom hE m m' k hk 0 0
          (fun t => φ ⟨(t, m - t), by ring⟩ ≫ f t ≫
            eqToHom (congrArg (fun u => dual (C.X (m - u))) (add_zero t).symm))
          (fun t => θ ⟨(t, m' - t), by ring⟩ ≫ g t ≫
            eqToHom (congrArg (fun u => dual (E.X (m' - u))) (add_zero t).symm)) r ≫
        eqToHom (congrArg (fun u => dual ((basedComplexTensor C E hE).X (k - u)))
          (show r + (0 + 0) = r by ring)) := by
  have hrk : r + (k - r) = k := by ring
  refine block_ext fun a p => ?_
  refine (block_comp _ _ a p).trans ?_
  refine Eq.trans (Finset.sum_congr rfl fun q _ => congrArg₂ (· ≫ ·)
    (blockInc_comp_basedStrProd_comp_blockProj hE m m' k hk φ θ r (k - r) hrk a q)
    (blockInc_comp_basedDualProd_comp_blockProj hE m m' k hk f g r q p)) ?_
  refine Eq.trans ?_ (blockInc_comp_basedDualTensorHom_comp_eqToHom_comp_blockProj hE m m' k hk
    0 0 _ _ r r (by ring) a p).symm
  by_cases hp : ((p : ℕ) : ℤ) = (a : ℕ) - 0
  · have hpa : p = a := Fin.ext (by omega)
    subst hpa
    have hp' : (((p : ℕ) : ℤ) = (p : ℕ) - 0) = True := eq_true (by ring)
    have hs : (r - (m - ((p : ℕ) : ℤ)) + 0) * (m - ((p : ℕ) : ℤ) + 0 + m) +
        0 * (m - ((p : ℕ) : ℤ)) + (r - (m - ((p : ℕ) : ℤ))) * (m - ((p : ℕ) : ℤ) + m) =
        2 * ((r - (m - ((p : ℕ) : ℤ))) * (m - ((p : ℕ) : ℤ) + m)) := by ring
    simp only [hp', ↓reduceDIte, hs, Int.negOnePow_two_mul, one_smul]
    by_cases hin : 0 ≤ m - (p : ℕ) ∧ m - (p : ℕ) ≤ (r.toNat : ℤ)
    · rw [Finset.sum_eq_single (⟨(m - (p : ℕ)).toNat, by omega⟩ : Fin (r.toNat + 1))]
      · have hq : (((p : ℕ) : ℤ) =
            m - (((⟨(m - (p : ℕ)).toNat, by omega⟩ : Fin (r.toNat + 1)) : ℕ) : ℤ)) = True :=
          eq_true (by simp only; omega)
        simp only [hq, ↓reduceDIte, Linear.units_smul_comp, Linear.comp_units_smul, smul_smul,
          Int.units_mul_self, one_smul, Category.assoc]
        exact kron_through' φ θ f g (by omega) (by dsimp only; omega) (by omega)
          (by dsimp only; omega) _ _ _ _ _ _ _ _ _ _
      · intro q _ hq
        have hq' : ¬ (((p : ℕ) : ℤ) = m - (q : ℕ)) := fun h' => hq (Fin.ext (by simp only; omega))
        simp only [hq', ↓reduceDIte, zero_comp]
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [Finset.sum_eq_zero]
      · symm
        rw [not_and_or] at hin
        rcases hin with hin | hin
        · rw [comp_eq_zero_of_dim (φ _) _ (by
              change (C.X (m - ((p : ℕ) : ℤ))).dim = 0; exact hC _ (by omega)),
            basedKron_eq_zero (Or.inl rfl), zero_comp, comp_zero]
        · rw [comp_eq_zero_of_dim (θ _) _ (by
              change (E.X (r - (m - ((p : ℕ) : ℤ)))).dim = 0; exact hE _ (by omega)),
            basedKron_eq_zero (Or.inr rfl), zero_comp, comp_zero]
      · intro q _
        have hq' : ¬ (((p : ℕ) : ℤ) = m - (q : ℕ)) := fun h' => hin ⟨by omega, by omega⟩
        simp only [hq', ↓reduceDIte, zero_comp]
  · have hp' : ¬ (((p : ℕ) : ℤ) = (a : ℕ) - 0) := hp
    simp only [hp', ↓reduceDIte]
    refine Finset.sum_eq_zero fun q _ => ?_
    by_cases hq : ((a : ℕ) : ℤ) = m - (q : ℕ)
    · have hq' : ¬ (((p : ℕ) : ℤ) = m - (q : ℕ)) := by omega
      simp only [hq', ↓reduceDIte, comp_zero]
    · simp only [hq, ↓reduceDIte, zero_comp]

end HSP.ChainModels
