import Mathlib
import HilbertSmithPaper.ChainModels.Grid.CubicalTorusGrid
import HilbertSmithPaper.LTheory.Base.Complexes.DualComplex
import HilbertSmithPaper.LTheory.Base.Complexes.StructureComplex
import HilbertSmithPaper.LTheory.Base.Complexes.StructureInvolution
import HilbertSmithPaper.Categories.Asymptotic.Propagation

/-!
# Circle duality

On `S = S_k`, the structure `φ ∈ M(S)_1` (`φ([w]^*) = e_{w-1}`, `φ(e_w^*) = [w]`), the element
`H ∈ M(S)_2` (`H(e_w^*) = e_w`, `H([w]^*) = 0`), `φ^s = φ + ½ ∂H`, the inverse `b`
(`b(e_w) = [w+1]^*`, `b([w]) = e_w^*`) and the homotopies `K = ½ H b`, `K' = ½ b H`, with their
five properties.

## Encoding

* Components are matrices between based vector spaces (the dual of `ℚ^d` is `ℚ^d`), written by
  their entries in terms of the indices `w ∈ Fin k`: `φ_{0,1}` is the identity matrix,
  `φ_{1,0}` has entry `1` at (row `e_{w-1}`, column `[w]^*`), `H_{1,1}` is the identity matrix,
  and all other components are zero (their objects are zero-dimensional).
* `circleB k r : S_r → (S^{1-*})_r` is the degree-`r` component of `b`; `circleK k r : S_r →
  S_{r+1}` and `circleK' k r : (S^{1-*})_r → (S^{1-*})_{r+1}` are the homotopies. In the
  homotopy identities the incoming term `K_{r-1}` is followed by the identity transport
  `S_{r-1+1} = S_r`.
* Labels: the cell `[w]` and its dual sit at `4w/k`, the cell `e_w` and its dual at `(4w+2)/k`
  (`circleLabel`); propagation is measured in `ℝ/4ℤ`, and `h/2 = 2/k`.
-/

open CategoryTheory
open scoped NNReal

namespace HSP.ChainModels

open FreeQ DualCat

variable (k : ℕ)

/-- The structure `φ ∈ M(S_k)_1`: `φ(e_w^*) = [w]` and `φ([w]^*) = e_{w-1}`. -/
def circlePhi : (StructureCx (circleComplex k)).X 1 :=
  fun x => ofMatrix (Matrix.of fun a b =>
    if x.1.1 = 0 then (if (a : ℕ) = b then 1 else 0)
    else if x.1.1 = 1 then (if (a : ℕ) = ((b : ℕ) + k - 1) % k then 1 else 0) else 0)

/-- The element `H ∈ M(S_k)_2`: `H(e_w^*) = e_w`, `H([w]^*) = 0`. -/
def circleH : (StructureCx (circleComplex k)).X 2 :=
  fun x => ofMatrix (Matrix.of fun a b =>
    if x.1.1 = 1 then (if (a : ℕ) = b then 1 else 0) else 0)

/-- The symmetric structure `φ^s = φ + ½ ∂H`. -/
def circlePhiSym : (StructureCx (circleComplex k)).X 1 :=
  circlePhi k + (1 / 2 : ℚ) • (StructureCx (circleComplex k)).d 2 1 (circleH k)

/-- The component `b_r : S_r → (S^{1-*})_r` of the inverse `b`: `b(e_w) = [w+1]^*`,
`b([w]) = e_w^*`. -/
def circleB (r : ℤ) : (circleComplex k).X r ⟶ (dualCx (circleComplex k) 1).X r :=
  ofMatrix (Matrix.of fun a b =>
    if r = 1 then (if (a : ℕ) = ((b : ℕ) + 1) % k then 1 else 0)
    else if r = 0 then (if (a : ℕ) = b then 1 else 0) else 0)

/-- The homotopy `K = ½ H b`, in degree `r`: `S_r → S_{r+1}`. -/
def circleK (r : ℤ) : (circleComplex k).X r ⟶ (circleComplex k).X (r + 1) :=
  (1 / 2 : ℚ) • (circleB k r ≫ circleH k ⟨(r + 1, 1 - r), by ring⟩)

/-- The homotopy `K' = ½ b H`, in degree `r`: `(S^{1-*})_r → (S^{1-*})_{r+1}`. -/
def circleK' (r : ℤ) :
    (dualCx (circleComplex k) 1).X r ⟶ (dualCx (circleComplex k) 1).X (r + 1) :=
  (1 / 2 : ℚ) • (circleH k ⟨(r + 1, 1 - r), by ring⟩ ≫ circleB k (r + 1))

/-- The label of a cell of `S_{k,r}` (and of its dual): its center, `4w/k` or `(4w+2)/k`. -/
noncomputable def circleLabel (r : ℤ) (a : Fin ((circleComplex k).X r).dim) :
    AddCircle (4 : ℝ) :=
  ((4 * ((circleCell k r a).1 : ℕ) + if (circleCell k r a).2 then 2 else 0) / k : ℝ)

/-- **Circle duality.** For the circle complex `S = S_k`:
1. `∂φ = 0`, and `φ_♮ : S^{1-*} → S` is an isomorphism with inverse `b`;
2. `Tφ = φ + ∂H`, so `φ^s = ½(φ + Tφ)`, `∂φ^s = 0` and `Tφ^s = φ^s`;
3. `φ^s b - 1 = dK + Kd` and `b φ^s - 1 = dK' + K'd`;
4. `ε φ^s(e_w^*) = 1 = e_w^*(∑_v e_v)`;
5. with cells and duals labelled at the centers, `φ`, `φ^s`, `b`, `H`, `K`, `K'` have propagation
   at most `h/2 = 2/k`. -/
theorem circle_duality :
    -- (1)
    ((StructureCx (circleComplex k)).d 1 0 (circlePhi k) = 0 ∧
      ∀ r : ℤ, circlePhi k ⟨(r, 1 - r), by ring⟩ ≫ circleB k r = 𝟙 _ ∧
        circleB k r ≫ circlePhi k ⟨(r, 1 - r), by ring⟩ = 𝟙 _) ∧
    -- (2)
    ((StructureCx.T (circleComplex k)).f 1 (circlePhi k) =
        circlePhi k + (StructureCx (circleComplex k)).d 2 1 (circleH k) ∧
      circlePhiSym k = (1 / 2 : ℚ) • (circlePhi k + (StructureCx.T (circleComplex k)).f 1
        (circlePhi k)) ∧
      (StructureCx (circleComplex k)).d 1 0 (circlePhiSym k) = 0 ∧
      (StructureCx.T (circleComplex k)).f 1 (circlePhiSym k) = circlePhiSym k) ∧
    -- (3)
    (∀ r : ℤ, circleB k r ≫ circlePhiSym k ⟨(r, 1 - r), by ring⟩ - 𝟙 _ =
        circleK k r ≫ (circleComplex k).d (r + 1) r +
          (circleComplex k).d r (r - 1) ≫ circleK k (r - 1) ≫
            eqToHom (congrArg (circleComplex k).X (by ring))) ∧
    (∀ r : ℤ, circlePhiSym k ⟨(r, 1 - r), by ring⟩ ≫ circleB k r - 𝟙 _ =
        circleK' k r ≫ (dualCx (circleComplex k) 1).d (r + 1) r +
          (dualCx (circleComplex k) 1).d r (r - 1) ≫ circleK' k (r - 1) ≫
            eqToHom (congrArg (dualCx (circleComplex k) 1).X (by ring))) ∧
    -- (4)
    (circlePhiSym k ⟨(0, 1), by ring⟩ ≫ circleAug k = ofMatrix (Matrix.of fun _ _ => 1) ∧
      dualHom (circleFundamental k) = ofMatrix (Matrix.of fun _ _ => 1)) ∧
    -- (5)
    ((∀ x, (prop (circleLabel k x.1.2) (circleLabel k x.1.1) (circlePhi k x) : ℝ) ≤ 2 / k) ∧
      (∀ x, (prop (circleLabel k x.1.2) (circleLabel k x.1.1) (circlePhiSym k x) : ℝ) ≤ 2 / k) ∧
      (∀ x, (prop (circleLabel k x.1.2) (circleLabel k x.1.1) (circleH k x) : ℝ) ≤ 2 / k) ∧
      (∀ r, (prop (circleLabel k r) (circleLabel k (1 - r)) (circleB k r) : ℝ) ≤ 2 / k) ∧
      (∀ r, (prop (circleLabel k r) (circleLabel k (r + 1)) (circleK k r) : ℝ) ≤ 2 / k) ∧
      (∀ r, (prop (circleLabel k (1 - r)) (circleLabel k (1 - (r + 1))) (circleK' k r) : ℝ) ≤
        2 / k)) := by
  sorry

end HSP.ChainModels
