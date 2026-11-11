import Mathlib
import HilbertSmithPaper.ChainModels.Grid.ChainModelDuality
import HilbertSmithPaper.ChainModels.Grid.ChainModel
import HilbertSmithPaper.Categories.Asymptotic.Propagation
import HilbertSmithPaper.LTheory.Localization.Products.BasedTensor
import HilbertSmithPaper.LTheory.Base.Complexes.StructureInvolution

/-!
# The chain model is Poincaré

For every `i`: `∂φ_i = 0` and `Tφ_i = φ_i`; `b_i` is a chain map and the exact inverse of
`(φ_i^u)_♮`, `φ_i^u` the product of the unsymmetrized circle structures; the homotopies `H_i`,
`H'_i` satisfy `φ_i b_i - 1 = dH_i + H_i d` and `b_i φ_i - 1 = dH'_i + H'_i d`; with cells labelled
at their centers, `φ_i`, `b_i`, `H_i`, `H'_i` have `d_∞`-propagation at most `h_i`; and
`ε φ_i(α) = α(z_i)` for `α ∈ D_N^*`.

## Encoding

* Tensors of maps, in the explicit bases of the tensor product of based complexes:
  `basedTensorHom` is `f ⊗ g` for maps of degrees `d`, `e`, with
  `(f ⊗ g)(x ⊗ y) = (-1)^{|g||x|} f(x) ⊗ g(y)`; `basedDualTensorHom` is `Ξ^{-1}(F ⊗ G)Ξ` on
  `(C ⊗ E)^{k-*}` for maps `F`, `G` of `C^{m-*}`, `E^{m'-*}`, with the signs
  `s(a,b) = (-1)^{b(a+m)}` of `Ξ`.
* The homotopies are built by the telescoping recursion over `C(k) = (⋯(𝟙 ⊗ S) ⋯) ⊗ S`:
  `H^{(j+1)} = H^{(j)} ⊗ A + 1 ⊗ K` with `A = φ^s b`, and `H_i = H^{(n)} ⊗ 1_P`; this unfolds to
  `∑_j 1^{⊗(j-1)} ⊗ K ⊗ A^{⊗(n-j)} ⊗ 1_P`. Likewise `H'_i` with `A' = b φ^s` and `K'` through `Ξ`.
  Maps of degree `0` and `1` are written with the target degree `r + 0`, `r + 1`, with identity
  transports where needed.
* `ε` on `(D_i)_0 = C(k_i)_0 ⊠ P_0` is `ε^{⊗n} ⊠ ε_P`; `α ↦ α(z_i)` is the transpose of the
  column `z_i`.
-/

open CategoryTheory
open scoped NNReal

namespace HSP.ChainModels

open FreeQ DualCat

section TensorHom

variable {C C' E E' : ChainComplex FreeQ ℤ}

/-- The tensor `f ⊗ g` of maps of degrees `d` and `e`: on `C_a ⊠ E_c` it is
`(-1)^{e a} f_a ⊠ g_c` into `C'_{a+d} ⊠ E'_{c+e}`. -/
noncomputable def basedTensorHom (hE : ∀ q < 0, (E.X q).dim = 0)
    (hE' : ∀ q < 0, (E'.X q).dim = 0) (d e : ℤ) (f : ∀ r, C.X r ⟶ C'.X (r + d))
    (g : ∀ r, E.X r ⟶ E'.X (r + e)) (r : ℤ) :
    (basedComplexTensor C E hE).X r ⟶ (basedComplexTensor C' E' hE').X (r + (d + e)) :=
  ∑ a : Fin (r.toNat + 1), ∑ a' : Fin ((r + (d + e)).toNat + 1),
    if h : ((a' : ℕ) : ℤ) = (a : ℕ) + d then
      (e * (a : ℕ)).negOnePow •
        (blockProj (tensorSummandDim C E r) a ≫ basedKron (f (a : ℕ)) (g (r - (a : ℕ))) ≫
          eqToHom (by
            simp only [tensorSummandDim]
            rw [h, show r + (d + e) - (((a : ℕ) : ℤ) + d) = r - ((a : ℕ) : ℤ) + e by ring]) ≫
          blockInc (tensorSummandDim C' E' (r + (d + e))) a')
    else 0

/-- The map `Ξ^{-1}(F ⊗ G)Ξ` of `(C ⊗ E)^{k-*}`, `m + m' = k`, for maps `F` of `C^{m-*}` and `G`
of `E^{m'-*}` of degrees `d`, `e`: from the dual of `C_{m-a} ⊠ E_{m'-b}` to the dual of
`C_{m-a-d} ⊠ E_{m'-b-e}` it is `s(a+d,b+e) (-1)^{e a} s(a,b) F_a ⊠ G_b`. -/
noncomputable def basedDualTensorHom (hE : ∀ q < 0, (E.X q).dim = 0) (m m' k : ℤ)
    (hk : m + m' = k) (d e : ℤ) (F : ∀ r, dual (C.X (m - r)) ⟶ dual (C.X (m - (r + d))))
    (G : ∀ r, dual (E.X (m' - r)) ⟶ dual (E.X (m' - (r + e)))) (r : ℤ) :
    dual ((basedComplexTensor C E hE).X (k - r)) ⟶
      dual ((basedComplexTensor C E hE).X (k - (r + (d + e)))) :=
  ∑ p : Fin ((k - r).toNat + 1), ∑ p' : Fin ((k - (r + (d + e))).toNat + 1),
    if h : ((p' : ℕ) : ℤ) = (p : ℕ) - d then
      (((r - (m - (p : ℕ))) + e) * ((m - (p : ℕ)) + d + m) + e * (m - (p : ℕ)) +
          (r - (m - (p : ℕ))) * ((m - (p : ℕ)) + m)).negOnePow •
        (blockProj (tensorSummandDim C E (k - r)) p ≫
          eqToHom (by
            simp only [tensorSummandDim, dual_eq]
            rw [show m - (m - ((p : ℕ) : ℤ)) = ((p : ℕ) : ℤ) by ring,
              show m' - (r - (m - ((p : ℕ) : ℤ))) = k - r - ((p : ℕ) : ℤ) by omega]) ≫
          basedKron (F (m - (p : ℕ))) (G (r - (m - (p : ℕ)))) ≫
          eqToHom (by
            simp only [tensorSummandDim, dual_eq]
            rw [h, show m - (m - ((p : ℕ) : ℤ) + d) = ((p : ℕ) : ℤ) - d by ring,
              show m' - (r - (m - ((p : ℕ) : ℤ)) + e) = k - (r + (d + e)) - (((p : ℕ) : ℤ) - d) by
                omega]) ≫
          blockInc (tensorSummandDim C E (k - (r + (d + e)))) p')
    else 0

end TensorHom

/-! ### The unsymmetrized structure, the homotopies and the augmentation -/

/-- The iterated unsymmetrized structure `(⋯(φ ⊗ φ) ⊗ ⋯) ⊗ φ ∈ M(C(k))_n`. -/
noncomputable def gridStructureU (k : ℕ) : ∀ n : ℕ, (StructureCx (gridComplex k n)).X (n : ℤ)
  | 0 => unitStructure
  | n + 1 => basedStrProd (gridComplex k n) (circleComplex k) (circleComplex_dim_neg k) n 1
      ((n + 1 : ℕ) : ℤ) (by push_cast; ring) (gridStructureU k n) (circlePhi k)

/-- `A = φ^s b` on `S_k`, as a map of degree `0`. -/
def circleA (k : ℕ) (r : ℤ) : (circleComplex k).X r ⟶ (circleComplex k).X (r + 0) :=
  circleB k r ≫ circlePhiSym k ⟨(r, 1 - r), by ring⟩ ≫
    eqToHom (congrArg (circleComplex k).X (add_zero r).symm)

/-- `A' = b φ^s` on `S_k^{1-*}`, as a map of degree `0`. -/
def circleA' (k : ℕ) (r : ℤ) :
    dual ((circleComplex k).X (1 - r)) ⟶ dual ((circleComplex k).X (1 - (r + 0))) :=
  circlePhiSym k ⟨(r, 1 - r), by ring⟩ ≫ circleB k r ≫
    eqToHom (by rw [add_zero])

/-- The identity of a complex, as a map of degree `0`. -/
def idDeg0 (C : ChainComplex FreeQ ℤ) (r : ℤ) : C.X r ⟶ C.X (r + 0) :=
  eqToHom (congrArg C.X (add_zero r).symm)

/-- The identity of a dual complex `C^{m-*}`, as a map of degree `0`. -/
def idDualDeg0 (C : ChainComplex FreeQ ℤ) (m r : ℤ) : dual (C.X (m - r)) ⟶ dual (C.X (m - (r + 0))) :=
  eqToHom (by rw [add_zero])

/-- The homotopy `H^{(n)} = ∑_j 1^{⊗(j-1)} ⊗ K ⊗ A^{⊗(n-j)}` on `C(k)`, by the recursion
`H^{(n+1)} = H^{(n)} ⊗ A + 1 ⊗ K`. -/
noncomputable def gridH (k : ℕ) : ∀ (n : ℕ) (r : ℤ), (gridComplex k n).X r ⟶ (gridComplex k n).X (r + 1)
  | 0, _ => 0
  | n + 1, r =>
    basedTensorHom (circleComplex_dim_neg k) (circleComplex_dim_neg k) 1 0 (gridH k n)
        (circleA k) r ≫ eqToHom (congrArg (gridComplex k (n + 1)).X (by ring)) +
      basedTensorHom (circleComplex_dim_neg k) (circleComplex_dim_neg k) 0 1
        (idDeg0 (gridComplex k n)) (circleK k) r ≫
        eqToHom (congrArg (gridComplex k (n + 1)).X (by ring))

/-- The homotopy `H'^{(n)} = Ξ^{-1}(∑_j 1^{⊗(j-1)} ⊗ K' ⊗ A'^{⊗(n-j)})Ξ` on `C(k)^{n-*}`. -/
noncomputable def gridH' (k : ℕ) : ∀ (n : ℕ) (r : ℤ),
    dual ((gridComplex k n).X ((n : ℤ) - r)) ⟶ dual ((gridComplex k n).X ((n : ℤ) - (r + 1)))
  | 0, _ => 0
  | n + 1, r =>
    basedDualTensorHom (circleComplex_dim_neg k) n 1 ((n + 1 : ℕ) : ℤ) (by push_cast; ring) 1 0
        (gridH' k n) (circleA' k) r ≫
        eqToHom (congrArg (fun t => dual ((gridComplex k (n + 1)).X (((n + 1 : ℕ) : ℤ) - t)))
          (show r + (1 + 0) = r + 1 by ring)) +
      basedDualTensorHom (circleComplex_dim_neg k) n 1 ((n + 1 : ℕ) : ℤ) (by push_cast; ring) 0 1
        (idDualDeg0 (gridComplex k n) n) (circleK' k) r ≫
        eqToHom (congrArg (fun t => dual ((gridComplex k (n + 1)).X (((n + 1 : ℕ) : ℤ) - t)))
          (show r + (0 + 1) = r + 1 by ring))

private lemma cp2Complex_dim_neg'' : ∀ q < 0, (cp2Complex.X q).dim = 0 := by
  intro q hq
  rcases q with q | q
  · exact absurd hq (by simp)
  · rfl

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- The unsymmetrized structure `φ_i^u = (⋯(φ ⊗ φ) ⊗ ⋯ ⊗ φ) ⊗ φ_P ∈ M(D_i)_N`. -/
noncomputable def chainModelStructureU (A : LocalDatum p n D ρplus) (i : ℕ) :
    (StructureCx (chainModel A i)).X ((n + 4 : ℕ) : ℤ) :=
  basedStrProd (gridComplex (meshSequence A i) n) cp2Complex cp2Complex_dim_neg'' n 4
    ((n + 4 : ℕ) : ℤ) (by push_cast; ring) (gridStructureU (meshSequence A i) n) cp2Structure

/-- The homotopy `H_i = H^{(n)} ⊗ 1_P` on `D_i`, in degree `r`. -/
noncomputable def chainModelH (A : LocalDatum p n D ρplus) (i : ℕ) (r : ℤ) :
    (chainModel A i).X r ⟶ (chainModel A i).X (r + 1) :=
  basedTensorHom cp2Complex_dim_neg'' cp2Complex_dim_neg'' 1 0 (gridH (meshSequence A i) n)
      (idDeg0 cp2Complex) r ≫ eqToHom (congrArg (chainModel A i).X (by ring))

/-- The homotopy `H'_i = Ξ^{-1}(H'^{(n)} ⊗ 1_{P^{4-*}})Ξ` on `D_i^{N-*}`, in degree `r`. -/
noncomputable def chainModelH' (A : LocalDatum p n D ρplus) (i : ℕ) (r : ℤ) :
    (dualCx (chainModel A i) ((n + 4 : ℕ) : ℤ)).X r ⟶
      (dualCx (chainModel A i) ((n + 4 : ℕ) : ℤ)).X (r + 1) :=
  basedDualTensorHom cp2Complex_dim_neg'' n 4 ((n + 4 : ℕ) : ℤ) (by push_cast; ring) 1 0
      (gridH' (meshSequence A i) n) (idDualDeg0 cp2Complex 4) r ≫
    eqToHom (congrArg (fun t => dual ((chainModel A i).X (((n + 4 : ℕ) : ℤ) - t)))
      (show r + (1 + 0) = r + 1 by ring))

/-- The augmentation `ε = ε^{⊗n} ⊠ ε_P : (D_i)_0 → ℚ`. -/
noncomputable def chainModelAug (A : LocalDatum p n D ρplus) (i : ℕ) :
    (chainModel A i).X 0 ⟶ (⟨1⟩ : FreeQ) :=
  blockProj _ (0 : Fin 1) ≫ basedKron (gridAug (meshSequence A i) n) cp2Aug

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
      dualHom (chainModelFundamental A i)) := by
  sorry

end HSP.ChainModels
