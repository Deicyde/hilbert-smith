import Mathlib
import HilbertSmithPaper.ChainModels.Grid.ChainModelPoincare
import HilbertSmithPaper.ChainModels.Grid.Poincare.ChainModelH
import HilbertSmithPaper.ChainModels.Grid.Poincare.ChainModelHDual
import HilbertSmithPaper.Categories.Asymptotic.AsymptoticDuality
import HilbertSmithPaper.LTheory.Base.Pairs.SymmetricPoincareComplex
import HilbertSmithPaper.Corner.RoundSphere
import HilbertSmithPaper.ChainModels.Grid.Model.ChainModelLabel

/-!
# The labelled chain model is Poincaré

For a continuous `c : 𝕋ⁿ → Sⁿ`, give the basis cell `b` of `D_i` (and its dual) the label
`c(x_b)`. Then `(D_i, φ_i)_i` is a strict `N`-dimensional symmetric Poincaré complex in
`𝒜_𝟏(Sⁿ)`, concentrated in `[0, N]`, with inverse `b_i` and homotopies `H_i`, `H'_i`.

## Encoding

* `labelledPre A c r` is the object of `𝒜_𝟏(Sⁿ)` (before the quotient) with based module
  `(D_i)_r` at level `i` and labels `c(x_b)`, `x_b` the torus label of `b`; `labelledObj A c r`
  is its class in `AsymCat (GroupSeq.trivial p) (RoundSphere n)`. As `M^* = M` in `𝒜_𝟏(Sⁿ)`,
  the dual cells of `(D_i^{N-*})_r = ((D_i)_{N-r})^*` carry the labels of `(D_i)_{N-r}`.
* `unitMat` reads a rational matrix as an equivariant matrix for the trivial group (the basis
  `Unit × Fin m`).
* `IsChainModelRep A c f m` says that the morphism `f` of `𝒜_𝟏(Sⁿ)` between labelled objects is
  the class of the sequence of matrices `m_i`: some representative has coordinates exactly
  `m_i`. Its existence contains the propagation estimate `prop(m_i) → 0`.
* The lemma `labelledModel_poincare` asserts a strict symmetric Poincaré complex `P` of dimension
  `N = n + 4` whose objects are the labelled objects, whose differential and structure are the
  classes of `d` and `φ_i`, and a homotopy equivalence `φ_♮ : P^{N-*} ⟶ P` (Mathlib's
  `HomotopyEquiv`) whose inverse is the class of `b_i` and whose homotopies `b φ ≃ 1` on `P` and
  `φ b ≃ 1` on `P^{N-*}` are the classes of `H_i` and `H'_i` (`chainModel_poincare`).
-/

open CategoryTheory

namespace HSP.Evaluation

open HSP.ChainModels HSP.FreeQ

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- The labelled object in degree `r`: `(D_i)_r` at level `i`, the basis cell `b` labelled
`c(x_b) ∈ Sⁿ`. -/
noncomputable def labelledPre (A : LocalDatum p n D ρplus)
    (c : C(Torus n, Corner.RoundSphere n)) (r : ℤ) :
    AsymPre (GroupSeq.trivial p) (Corner.RoundSphere n) where
  n i := ((chainModel A i).X r).dim
  x i b := c (chainModelLabel A i r b)

/-- The labelled object in degree `r`, in `𝒜_𝟏(Sⁿ)`. -/
noncomputable abbrev labelledObj (A : LocalDatum p n D ρplus)
    (c : C(Torus n, Corner.RoundSphere n)) (r : ℤ) :
    AsymCat (GroupSeq.trivial p) (Corner.RoundSphere n) :=
  ⟨labelledPre A c r⟩

/-- A rational matrix as an equivariant matrix for the trivial group. -/
def unitMat {m k : ℕ} (u : Matrix (Fin m) (Fin k) ℚ) : Matrix (Unit × Fin m) (Unit × Fin k) ℚ :=
  fun a b => u a.2 b.2

/-- The morphism `f` of `𝒜_𝟏(Sⁿ)` between labelled objects is the class of the sequence of
matrices `m_i`. -/
def IsChainModelRep (A : LocalDatum p n D ρplus) (c : C(Torus n, Corner.RoundSphere n))
    {r s : ℤ} (f : labelledObj A c r ⟶ labelledObj A c s)
    (m : ∀ i, Matrix (Fin ((chainModel A i).X s).dim) (Fin ((chainModel A i).X r).dim) ℚ) :
    Prop :=
  ∃ u : labelledPre A c r ⟶ labelledPre A c s,
    (∀ i, FreeCat.mat (AsymPre.coord u i) = unitMat (m i)) ∧ f = AsymCat.mkHom u

/-- **The labelled chain model is Poincaré.** For a continuous `c : 𝕋ⁿ → Sⁿ`, labelling the
cells of `D_i` and their duals by `c(x_b)` makes `(D_i, φ_i)_i` a strict `N`-dimensional symmetric
Poincaré complex in `𝒜_𝟏(Sⁿ)`, concentrated in `[0, N]`, `N = n + 4`, whose inverse is `b_i`
with homotopies `H_i`, `H'_i`. -/
theorem labelledModel_poincare (A : LocalDatum p n D ρplus)
    (c : C(Torus n, Corner.RoundSphere n)) :
    ∃ (P : SymPoincare (AsymCat (GroupSeq.trivial p) (Corner.RoundSphere n)) ((n + 4 : ℕ) : ℤ))
      (hX : ∀ r, P.C.X r = labelledObj A c r),
      (∀ r s, IsChainModelRep A c (eqToHom (hX r).symm ≫ P.C.d r s ≫ eqToHom (hX s))
        (fun i => toMatrix ((chainModel A i).d r s))) ∧
      (∀ x : {x : ℤ × ℤ // x.1 + x.2 = ((n + 4 : ℕ) : ℤ)},
        IsChainModelRep A c (eqToHom (hX x.1.2).symm ≫ P.φ x ≫ eqToHom (hX x.1.1))
          (fun i => toMatrix ((chainModelDuality A i).φ x))) ∧
      ∃ e : HomotopyEquiv (dualCx P.C ((n + 4 : ℕ) : ℤ)) P.C,
        e.hom = StructureCx.toHom P.φ P.cycle ∧
        (∀ r, IsChainModelRep A c (s := (n + 4 : ℕ) - r)
          (eqToHom (hX r).symm ≫ e.inv.f r ≫ eqToHom (hX ((n + 4 : ℕ) - r)))
          (fun i => toMatrix ((chainModelDuality A i).b r))) ∧
        (∀ r, IsChainModelRep A c
          (eqToHom (hX r).symm ≫ e.homotopyInvHomId.hom r (r + 1) ≫ eqToHom (hX (r + 1)))
          (fun i => toMatrix (chainModelH A i r))) ∧
        (∀ r, IsChainModelRep A c (r := (n + 4 : ℕ) - r) (s := (n + 4 : ℕ) - (r + 1))
          (eqToHom (hX ((n + 4 : ℕ) - r)).symm ≫ e.homotopyHomInvId.hom r (r + 1) ≫
            eqToHom (hX ((n + 4 : ℕ) - (r + 1))))
          (fun i => toMatrix (chainModelH' A i r))) := by
  sorry

end HSP.Evaluation
