import Mathlib
import HilbertSmithPaper.ChainModels.Grid.Tensor.StructureProducts.StrProdBlocks
import HilbertSmithPaper.ChainModels.Grid.Tensor.StructureProducts.DualProdBlocks
import HilbertSmithPaper.ChainModels.Grid.Tensor.StructureProducts.DualTensorHomBlocks
import HilbertSmithPaper.ChainModels.Grid.Tensor.StructureProducts.TensorHomTransportBlocks
import HilbertSmithPaper.ChainModels.Grid.Tensor.StructureProducts.ZeroDimComp
import HilbertSmithPaper.ChainModels.Grid.Tensor.BlockComp
import HilbertSmithPaper.ChainModels.Grid.Tensor.BlockExt
import HilbertSmithPaper.ChainModels.Grid.Tensor.KronComposite
import HilbertSmithPaper.ChainModels.Grid.Tensor.KronTransport
import HilbertSmithPaper.ChainModels.Grid.Tensor.KronZero

/-!
# A tensor between a product of structures and a product of duality maps

For a product of structures `φ ⊗ θ`, a tensor `F ⊗ G` of graded maps of degrees `d`, `e`, and a
product of duality maps `f ⊗ g`, the composite `(φ ⊗ θ) ≫ (F ⊗ G) ≫ (f ⊗ g)` is the dual tensor of
the factorwise composites `φ ≫ F ≫ f` and `θ ≫ G ≫ g`.

## Proof

Blockwise: each factor has at most one nonzero block from a given summand, and the three signs
`(-1)^{q(p+m)}`,
`(-1)^{ep}` and `(-1)^{(q+e)(p+d+m)}` multiply to the sign of the dual tensor. Out of
range, a factor passes through a zero-dimensional space.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP.ChainModels

open FreeQ DualCat

variable {C E : ChainComplex FreeQ ℤ}

variable (hE : ∀ q < 0, (E.X q).dim = 0)

private lemma kron_through3 {m m' d e : ℤ} (φ : (StructureCx C).X m) (θ : (StructureCx E).X m')
    (F : ∀ r, C.X r ⟶ C.X (r + d)) (G : ∀ r, E.X r ⟶ E.X (r + e))
    (f : ∀ r, C.X r ⟶ dual (C.X (m - r))) (g : ∀ r, E.X r ⟶ dual (E.X (m' - r)))
    {i i' j j' u u' v v' i2 u2 : ℤ} (hi : i = i') (hj : j = j') (hu : u = u') (hv : v = v')
    (hi2 : i2 = i + d) (hu2 : u2 = u + e)
    (hij : i + j = m) (hij' : i' + j' = m) (huv : u + v = m') (huv' : u' + v' = m')
    {W Z : FreeQ} (e0 : W = ⟨(dual (C.X j)).dim * (dual (E.X v)).dim⟩)
    (e2 : W = ⟨(dual (C.X j')).dim * (dual (E.X v')).dim⟩)
    (eM : (⟨(C.X (i + d)).dim * (E.X (u + e)).dim⟩ : FreeQ) = ⟨(C.X i2).dim * (E.X u2).dim⟩)
    (e1 : (⟨(dual (C.X (m - i2))).dim * (dual (E.X (m' - u2))).dim⟩ : FreeQ) = Z)
    (e3 : (⟨(dual (C.X (m - (i' + d)))).dim * (dual (E.X (m' - (u' + e)))).dim⟩ : FreeQ) = Z) :
    eqToHom e0 ≫ basedKron (φ ⟨(i, j), hij⟩) (θ ⟨(u, v), huv⟩) ≫ basedKron (F i) (G u) ≫
        eqToHom eM ≫ basedKron (f i2) (g u2) ≫ eqToHom e1 =
      eqToHom e2 ≫ basedKron (φ ⟨(i', j'), hij'⟩ ≫ F i' ≫ f (i' + d))
        (θ ⟨(u', v'), huv'⟩ ≫ G u' ≫ g (u' + e)) ≫ eqToHom e3 := by
  subst hi hj hu hv hi2 hu2 e0
  simp only [eqToHom_refl, Category.id_comp]
  rw [← basedKron_comp_basedKron, ← basedKron_comp_basedKron, Category.assoc, Category.assoc]

/-- *A tensor between a product of structures and a product of duality maps*:
`Ξ^{-1}(f ⊗ g)(F ⊗ G)(φ ⊗ θ)Ξ = Ξ^{-1}(fFφ ⊗ gGθ)Ξ`, with no sign. -/
theorem basedStrProd_comp_basedTensorHom_comp_basedDualProd (hC : ∀ q < 0, (C.X q).dim = 0)
    (m m' k : ℤ) (hk : m + m' = k) (φ : (StructureCx C).X m) (θ : (StructureCx E).X m')
    (d e : ℤ) (F : ∀ r, C.X r ⟶ C.X (r + d)) (G : ∀ r, E.X r ⟶ E.X (r + e))
    (f : ∀ r, C.X r ⟶ dual (C.X (m - r))) (g : ∀ r, E.X r ⟶ dual (E.X (m' - r)))
    (r s : ℤ) (h : r + (d + e) = s) :
    basedStrProd C E hE m m' k hk φ θ ⟨(r, k - r), by ring⟩ ≫ basedTensorHom hE hE d e F G r ≫
        eqToHom (congrArg (basedComplexTensor C E hE).X h) ≫ basedDualProd C E hE m m' k hk f g s =
      basedDualTensorHom hE m m' k hk d e
          (fun t => φ ⟨(t, m - t), by ring⟩ ≫ F t ≫ f (t + d))
          (fun t => θ ⟨(t, m' - t), by ring⟩ ≫ G t ≫ g (t + e)) r ≫
        eqToHom (congrArg (fun u => dual ((basedComplexTensor C E hE).X (k - u))) h) := by
  have hrk : r + (k - r) = k := by ring
  rw [← Category.assoc (basedTensorHom hE hE d e F G r)]
  refine block_ext fun a p => ?_
  refine (block_comp _ _ a p).trans ?_
  refine Eq.trans (Finset.sum_congr rfl fun q _ => congrArg₂ (· ≫ ·)
    (blockInc_comp_basedStrProd_comp_blockProj hE m m' k hk φ θ r (k - r) hrk a q)
    ((block_comp _ _ q p).trans (Finset.sum_congr rfl fun q' _ => congrArg₂ (· ≫ ·)
      (blockInc_comp_basedTensorHom_comp_eqToHom_comp_blockProj hE hE d e F G r s h q q')
      (blockInc_comp_basedDualProd_comp_blockProj hE m m' k hk f g s q' p)))) ?_
  refine Eq.trans ?_ (blockInc_comp_basedDualTensorHom_comp_eqToHom_comp_blockProj hE m m' k hk
    d e _ _ r s h a p).symm
  by_cases hp : ((p : ℕ) : ℤ) = (a : ℕ) - d
  · rw [dif_pos hp]
    by_cases hin : 0 ≤ m - (a : ℕ) ∧ m - (a : ℕ) ≤ (r.toNat : ℤ) ∧ 0 ≤ m - (a : ℕ) + d ∧
        m - (a : ℕ) + d ≤ (s.toNat : ℤ)
    · obtain ⟨h1, h2, h3, h4⟩ := hin
      set q0 : Fin (r.toNat + 1) := ⟨(m - (a : ℕ)).toNat, by omega⟩ with hq0
      set q1 : Fin (s.toNat + 1) := ⟨(m - (a : ℕ) + d).toNat, by omega⟩ with hq1
      have hq0v : ((q0 : ℕ) : ℤ) = m - (a : ℕ) := by simp only [hq0]; omega
      have hq1v : ((q1 : ℕ) : ℤ) = m - (a : ℕ) + d := by simp only [hq1]; omega
      rw [Finset.sum_eq_single q0]
      · rw [dif_pos (show ((a : ℕ) : ℤ) = m - (q0 : ℕ) by omega), Finset.sum_eq_single q1]
        · rw [dif_pos (show ((q1 : ℕ) : ℤ) = (q0 : ℕ) + d by omega),
            dif_pos (show ((p : ℕ) : ℤ) = m - (q1 : ℕ) by omega)]
          simp only [Linear.units_smul_comp, Linear.comp_units_smul, smul_smul, Category.assoc]
          have hs : ((s - (q1 : ℕ)) * ((q1 : ℕ) + m)).negOnePow * (e * (q0 : ℕ)).negOnePow *
              ((r - (q0 : ℕ)) * ((q0 : ℕ) + m)).negOnePow =
              (((r - (m - (a : ℕ))) + e) * ((m - (a : ℕ)) + d + m) + e * (m - (a : ℕ)) +
                (r - (m - (a : ℕ))) * ((m - (a : ℕ)) + m)).negOnePow := by
            rw [← Int.negOnePow_add, ← Int.negOnePow_add, hq0v, hq1v]
            congr 1
            rw [← h]
            ring
          rw [hs]
          congr 1
          exact kron_through3 φ θ F G f g hq0v (by dsimp only; omega) (by omega)
            (by dsimp only; omega) (by omega) (by omega) _ _ _ _ _ _ _ _ _
        · intro q' _ hq'
          rw [dif_neg (fun h' => hq' (Fin.ext (by omega))), zero_comp]
        · intro h'; exact absurd (Finset.mem_univ _) h'
      · intro q _ hq
        rw [dif_neg (fun h' => hq (Fin.ext (by omega))), zero_comp]
      · intro h'; exact absurd (Finset.mem_univ _) h'
    · rw [Finset.sum_eq_zero]
      · symm
        rw [basedKron_eq_zero, zero_comp, comp_zero, smul_zero]
        rw [not_and_or, not_and_or, not_and_or] at hin
        dsimp only
        rcases hin with h1 | h2 | h3 | h4
        · exact Or.inl (comp_eq_zero_of_dim _ _ (hC _ (by omega)))
        · exact Or.inr (comp_eq_zero_of_dim _ _ (hE _ (by omega)))
        · left
          rw [← Category.assoc]
          exact comp_eq_zero_of_dim _ _ (hC _ (by omega))
        · right
          rw [← Category.assoc]
          exact comp_eq_zero_of_dim _ _ (hE _ (by omega))
      · intro q _
        by_cases ha : ((a : ℕ) : ℤ) = m - (q : ℕ)
        · rw [dif_pos ha, Preadditive.comp_sum]
          refine Finset.sum_eq_zero fun q' _ => ?_
          by_cases hq' : ((q' : ℕ) : ℤ) = (q : ℕ) + d
          · have hq2 : (q : ℕ) < r.toNat + 1 := q.2
            have hq3 : (q' : ℕ) < s.toNat + 1 := q'.2
            exact absurd ⟨by omega, by omega, by omega, by omega⟩ hin
          · rw [dif_neg hq', zero_comp, comp_zero]
        · rw [dif_neg ha, zero_comp]
  · rw [dif_neg hp]
    refine Finset.sum_eq_zero fun q _ => ?_
    by_cases ha : ((a : ℕ) : ℤ) = m - (q : ℕ)
    · rw [dif_pos ha, Preadditive.comp_sum]
      refine Finset.sum_eq_zero fun q' _ => ?_
      by_cases hq' : ((q' : ℕ) : ℤ) = (q : ℕ) + d
      · rw [dif_pos hq', dif_neg (fun h' => hp (by omega)), comp_zero, comp_zero]
      · rw [dif_neg hq', zero_comp, comp_zero]
    · rw [dif_neg ha, zero_comp]

end HSP.ChainModels
