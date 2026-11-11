import Mathlib
import HilbertSmithPaper.ChainModels.Grid.Tensor.BasedDualTensorHom
import HilbertSmithPaper.ChainModels.Grid.Tensor.BlockDecomposition
import HilbertSmithPaper.ChainModels.Grid.Tensor.KronTransport
import HilbertSmithPaper.ChainModels.Grid.Poincare.GridFactor.IdDualDeg0


/-!
# Dual tensor of identities

The dual tensor `Ξ^{-1}(1 ⊗ 1)Ξ` of the identities of `C^{m-*}` and `E^{m'-*}`,
as maps of degree `0`,
is the identity of `(C ⊗ E)^{k-*}` (up to the identity transport `r = r + (0 + 0)`).

## Proof

The block from the summand `p` to the summand `p` is `s(a,b)^2` times a Kronecker product of
identities, that is the identity; all other blocks vanish.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP.ChainModels

open FreeQ DualCat

variable {C E : ChainComplex FreeQ ℤ}

private lemma sum_transport (hE : ∀ q < 0, (E.X q).dim = 0) {s t : ℤ} (h : s = t) :
    ∑ a : Fin (s.toNat + 1), blockProj (tensorSummandDim C E s) a ≫
      eqToHom (by subst h; rfl) ≫ blockInc (tensorSummandDim C E t) (Fin.cast (by rw [h]) a) =
    eqToHom (congrArg (basedComplexTensor C E hE).X h) := by
  subst h
  simp only [eqToHom_refl, Category.id_comp, Fin.cast_eq_self]
  exact blockProj_comp_blockInc_sum _

/-- *Dual tensor of identities*: `Ξ^{-1}(1 ⊗ 1)Ξ = 1` on `(C ⊗ E)^{k-*}`. -/
theorem basedDualTensorHom_id (hE : ∀ q < 0, (E.X q).dim = 0) (m m' k : ℤ) (hk : m + m' = k)
    (r : ℤ) :
    basedDualTensorHom hE m m' k hk 0 0 (idDualDeg0 C m) (idDualDeg0 E m') r =
      eqToHom (congrArg (fun u => dual ((basedComplexTensor C E hE).X (k - u)))
        (show r = r + (0 + 0) by ring)) := by
  refine Eq.trans ?_ (sum_transport hE (show k - r = k - (r + (0 + 0)) by ring))
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single (Fin.cast (by rw [show k - (r + (0 + 0)) = k - r by ring]) a)]
  · have h : (((Fin.cast (by rw [show k - (r + (0 + 0)) = k - r by ring]) a :
        Fin ((k - (r + (0 + 0))).toNat + 1)) : ℕ) : ℤ) = (a : ℕ) - 0 := by simp
    simp only [h, ↓reduceDIte]
    rw [Int.negOnePow_even _ ⟨(r - (m - ((a : ℕ) : ℤ))) * ((m - ((a : ℕ) : ℤ)) + m), by ring⟩,
      one_smul]
    simp only [idDualDeg0, basedKron_eqToHom, eqToHom_trans_assoc]
    rfl
  · intro b _ hb
    have h : ¬ (((b : ℕ) : ℤ) = (a : ℕ) - 0) := fun h =>
      hb (Fin.ext (by simp only [Fin.val_cast]; omega))
    simp only [h, ↓reduceDIte]
  · intro h; exact absurd (Finset.mem_univ _) h

end HSP.ChainModels
