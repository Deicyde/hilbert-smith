import Mathlib
import HilbertSmithPaper.ChainModels.Grid.Poincare.ChainModelPoincareCycle
import HilbertSmithPaper.ChainModels.Grid.Poincare.ChainModelPoincareInverse
import HilbertSmithPaper.ChainModels.Grid.Poincare.ChainModelPoincarePropagation
import HilbertSmithPaper.ChainModels.Grid.Poincare.ChainModelPoincareAugmentation
import HilbertSmithPaper.ChainModels.Grid.Model.ChainModelFundamental
import HilbertSmithPaper.ChainModels.Grid.Model.ChainModelLabel

/-!
# The chain model is Poincaré

For every `i`: `∂φ_i = 0` and `Tφ_i = φ_i`; `b_i` is a chain map and the exact inverse of
`(φ_i^u)_♮`, `φ_i^u` the product of the unsymmetrized circle structures; the homotopies `H_i`,
`H'_i` satisfy `φ_i b_i - 1 = dH_i + H_i d` and `b_i φ_i - 1 = dH'_i + H'_i d`; with cells labelled
at their centers, `φ_i`, `b_i`, `H_i`, `H'_i` have `d_∞`-propagation at most `h_i`; and
`ε φ_i(α) = α(z_i)` for `α ∈ D_N^*`.

## Encoding

* The four parts are separate lemmas (`chainModel_poincare_cycle`, `_inverse`, `_propagation`,
  `_augmentation`); this is their conjunction.
* The unsymmetrized structure, the homotopies and the augmentation (`chainModelStructureU`,
  `chainModelH`, `chainModelH'`, `chainModelAug`) have their own articles; tensors of maps are
  `basedTensorHom` and `basedDualTensorHom`.
-/

open CategoryTheory
open scoped NNReal

namespace HSP.ChainModels

open FreeQ DualCat

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- **The chain model is Poincaré.** For every `i`, with `N = n + 4` and `h_i = 4/k_i`:
1. `∂φ_i = 0` and `Tφ_i = φ_i`;
2. `b_i` is a chain map and the exact inverse of `(φ_i^u)_♮`; `φ_i b_i - 1 = dH_i + H_i d` and
   `b_i φ_i - 1 = dH'_i + H'_i d`;
3. with cells and duals labelled at their centers, `φ_i`, `b_i`, `H_i`, `H'_i` have
   `d_∞`-propagation at most `h_i`;
4. `ε φ_i(α) = α(z_i)` for every `α ∈ D_N^*`. -/
theorem chainModel_poincare (A : LocalDatum p n D ρplus) (i : ℕ) :
    -- (1)
    ((StructureCx (chainModel A i)).d ((n + 4 : ℕ) : ℤ) ((n + 4 : ℕ) - 1)
        (chainModelDuality A i).φ = 0 ∧
      (StructureCx.T (chainModel A i)).f ((n + 4 : ℕ) : ℤ) (chainModelDuality A i).φ =
        (chainModelDuality A i).φ) ∧
    -- (2)
    ((∀ r : ℤ, (chainModelDuality A i).b r ≫ (dualCx (chainModel A i) ((n + 4 : ℕ) : ℤ)).d r
        (r - 1) = (chainModel A i).d r (r - 1) ≫ (chainModelDuality A i).b (r - 1)) ∧
      (∀ r : ℤ, chainModelStructureU A i ⟨(r, (n + 4 : ℕ) - r), by ring⟩ ≫
          (chainModelDuality A i).b r = 𝟙 _ ∧
        (chainModelDuality A i).b r ≫ chainModelStructureU A i ⟨(r, (n + 4 : ℕ) - r), by ring⟩ =
          𝟙 _) ∧
      (∀ r : ℤ, (chainModelDuality A i).b r ≫
          (chainModelDuality A i).φ ⟨(r, (n + 4 : ℕ) - r), by ring⟩ - 𝟙 _ =
        chainModelH A i r ≫ (chainModel A i).d (r + 1) r +
          (chainModel A i).d r (r - 1) ≫ chainModelH A i (r - 1) ≫
            eqToHom (congrArg (chainModel A i).X (by ring))) ∧
      (∀ r : ℤ, (chainModelDuality A i).φ ⟨(r, (n + 4 : ℕ) - r), by ring⟩ ≫
          (chainModelDuality A i).b r - 𝟙 _ =
        chainModelH' A i r ≫ (dualCx (chainModel A i) ((n + 4 : ℕ) : ℤ)).d (r + 1) r +
          (dualCx (chainModel A i) ((n + 4 : ℕ) : ℤ)).d r (r - 1) ≫ chainModelH' A i (r - 1) ≫
            eqToHom (congrArg (dualCx (chainModel A i) ((n + 4 : ℕ) : ℤ)).X (by ring)))) ∧
    -- (3)
    ((∀ x, (prop (chainModelLabel A i x.1.2) (chainModelLabel A i x.1.1)
          ((chainModelDuality A i).φ x) : ℝ) ≤ 4 / meshSequence A i) ∧
      (∀ r, (prop (chainModelLabel A i r) (chainModelLabel A i ((n + 4 : ℕ) - r))
          ((chainModelDuality A i).b r) : ℝ) ≤ 4 / meshSequence A i) ∧
      (∀ r, (prop (chainModelLabel A i r) (chainModelLabel A i (r + 1)) (chainModelH A i r) : ℝ) ≤
        4 / meshSequence A i) ∧
      (∀ r, (prop (chainModelLabel A i ((n + 4 : ℕ) - r))
          (chainModelLabel A i ((n + 4 : ℕ) - (r + 1))) (chainModelH' A i r) : ℝ) ≤
        4 / meshSequence A i)) ∧
    -- (4)
    ((chainModelDuality A i).φ ⟨(0, (n + 4 : ℕ)), by ring⟩ ≫ chainModelAug A i =
      dualHom (chainModelFundamental A i)) :=
  ⟨chainModel_poincare_cycle A i, chainModel_poincare_inverse A i,
    chainModel_poincare_propagation A i, chainModel_poincare_augmentation A i⟩

end HSP.ChainModels
