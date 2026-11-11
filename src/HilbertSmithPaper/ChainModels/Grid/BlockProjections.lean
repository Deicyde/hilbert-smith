import Mathlib
import HilbertSmithPaper.ChainModels.Grid.BasedComplexTensor

/-!
# Block projections of the inclusions

For the concatenation `ℚ^{∑ d}` of blocks `ℚ^{d_j}`, with block inclusions `ι_j` and projections
`π_j`, `π_{j'} ι_j = δ_{j j'}`: the identity for `j = j'` and zero otherwise.

## Encoding

`blockInc_proj d` (the declaration of the article) is the conjunction of the two cases;
`blockInc_proj_self` and `blockInc_proj_ne` are the cases as `simp`/`reassoc` lemmas.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP.ChainModels

open FreeQ

private lemma blockInc_proj_apply {m : ℕ} (d : Fin m → ℕ) (j j' : Fin m) (b' : Fin (d j'))
    (b : Fin (d j)) :
    toMatrix (blockInc d j ≫ blockProj d j') b' b =
      if (⟨j', b'⟩ : (i : Fin m) × Fin (d i)) = ⟨j, b⟩ then 1 else 0 := by
  change ∑ a, (if finSigmaFinEquiv.symm a = ⟨j', b'⟩ then (1 : ℚ) else 0) *
    (if finSigmaFinEquiv.symm a = ⟨j, b⟩ then 1 else 0) = _
  rw [← Equiv.sum_comp finSigmaFinEquiv]
  simp only [Equiv.symm_apply_apply, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true]

/-- `π_{j'} ι_j = δ_{j j'}` for the blocks of `ℚ^{∑ d}`. -/
lemma blockInc_proj {m : ℕ} (d : Fin m → ℕ) :
    (∀ j, blockInc d j ≫ blockProj d j = 𝟙 _) ∧
      ∀ j j', j ≠ j' → blockInc d j ≫ blockProj d j' = 0 := by
  refine ⟨fun j => ?_, fun j j' h => ?_⟩
  · refine Matrix.ext fun b' b => ?_
    change toMatrix (blockInc d j ≫ blockProj d j) b' b = _
    rw [blockInc_proj_apply]
    simp only [Sigma.mk.injEq, heq_eq_eq, true_and]
    change _ = (1 : Matrix (Fin (d j)) (Fin (d j)) ℚ) b' b
    rw [Matrix.one_apply]
  · refine Matrix.ext fun b' b => ?_
    change toMatrix (blockInc d j ≫ blockProj d j') b' b = _
    rw [blockInc_proj_apply]
    split_ifs with he
    · exact absurd (congrArg Sigma.fst he).symm h
    · rfl

@[reassoc (attr := simp)]
lemma blockInc_proj_self {m : ℕ} (d : Fin m → ℕ) (j : Fin m) :
    blockInc d j ≫ blockProj d j = 𝟙 _ :=
  (blockInc_proj d).1 j

@[reassoc (attr := simp)]
lemma blockInc_proj_ne {m : ℕ} (d : Fin m → ℕ) {j j' : Fin m} (h : j ≠ j') :
    blockInc d j ≫ blockProj d j' = 0 :=
  (blockInc_proj d).2 j j' h

end HSP.ChainModels
