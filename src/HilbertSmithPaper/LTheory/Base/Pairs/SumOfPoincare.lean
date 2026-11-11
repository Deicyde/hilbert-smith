import HilbertSmithPaper.LTheory.Base.Pairs.SymmetricPoincareComplex
import HilbertSmithPaper.LTheory.Base.Complexes.SumOfComplexes

/-!
# Sums of Poincaré complexes

If `(C, φ)` and `(C', φ')` are strict `k`-dimensional symmetric Poincaré complexes, then so is
`(C ⊞ C', φ ⊕ φ')`; write `(C, φ) ⊕ (C', φ')` for it (`SymPoincare.sum`). Likewise `(C, -φ)`
(`SymPoincare.neg`) and the zero complex with the zero structure (`SymPoincare.zero`) are strict
`k`-dimensional symmetric Poincaré complexes.

Lean: the statement `SymPoincare.exists_sum` says that some `z : SymPoincare B k` has
`(z.C, z.φ) = (C ⊞ C', φ ⊕ φ')` in the Σ-type of structured complexes; `SymPoincare.sum` chooses
it (it is unique, the remaining fields being propositions).
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

open DualCat

universe v u

variable {B : Type u} [Category.{v} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B]

namespace SymPoincare

/-- The sum `(C ⊞ C', φ ⊕ φ')` of strict `k`-dimensional symmetric Poincaré complexes is a
strict `k`-dimensional symmetric Poincaré complex. -/
theorem exists_sum {k : ℤ} (x y : SymPoincare B k) :
    ∃ z : SymPoincare B k, (⟨z.C, z.φ⟩ : Σ C : ChainComplex B ℤ, (StructureCx C).X k) =
      ⟨x.C ⊞ y.C, StructureCx.sum x.φ y.φ⟩ := by
  sorry

/-- The sum `(C, φ) ⊕ (C', φ') = (C ⊞ C', φ ⊕ φ')`. -/
noncomputable def sum {k : ℤ} (x y : SymPoincare B k) : SymPoincare B k :=
  (exists_sum x y).choose

lemma sum_spec {k : ℤ} (x y : SymPoincare B k) :
    (⟨(sum x y).C, (sum x y).φ⟩ : Σ C : ChainComplex B ℤ, (StructureCx C).X k) =
      ⟨x.C ⊞ y.C, StructureCx.sum x.φ y.φ⟩ :=
  (exists_sum x y).choose_spec

private def negHomotopyEquiv {C D : ChainComplex B ℤ} (e : HomotopyEquiv C D) :
    HomotopyEquiv C D where
  hom := -e.hom
  inv := -e.inv
  homotopyHomInvId := (Homotopy.ofEq (Preadditive.neg_comp_neg _ _)).trans e.homotopyHomInvId
  homotopyInvHomId := (Homotopy.ofEq (Preadditive.neg_comp_neg _ _)).trans e.homotopyInvHomId

/-- The negative `(C, -φ)` of a strict `k`-dimensional symmetric Poincaré complex. -/
@[simps]
def neg {k : ℤ} (x : SymPoincare B k) : SymPoincare B k where
  C := x.C
  φ := -x.φ
  bounded := x.bounded
  cycle := by rw [map_neg, x.cycle, neg_zero]
  symmetric := by rw [map_neg, x.symmetric]
  poincare := by
    obtain ⟨e, he⟩ := x.poincare
    refine ⟨negHomotopyEquiv e, ?_⟩
    ext r
    change -e.hom.f r = -x.φ ⟨(r, k - r), _⟩
    rw [he]
    rfl

open ZeroObject in
/-- The zero complex. -/
private noncomputable def zeroCx : ChainComplex B ℤ where
  X _ := 0
  d _ _ := 0

private lemma isZero_dual {X : B} (hX : IsZero X) : IsZero (dual X) := by
  rw [IsZero.iff_id_eq_zero, ← dualHom_id, (IsZero.iff_id_eq_zero X).mp hX, dualHom_zero]

omit [Linear ℚ B] [DualCat B] in
private lemma isZero_zeroCx (r : ℤ) : IsZero ((zeroCx : ChainComplex B ℤ).X r) := isZero_zero B

/-- The zero complex with the zero structure, a strict `k`-dimensional symmetric Poincaré
complex. -/
noncomputable def zero (k : ℤ) : SymPoincare B k where
  C := zeroCx
  φ := 0
  bounded r _ := isZero_zeroCx r
  cycle := map_zero _
  symmetric := map_zero _
  poincare := by
    refine ⟨HomotopyEquiv.ofIso (HomologicalComplex.Hom.isoOfComponents
      (fun r => IsZero.iso (isZero_dual (isZero_zeroCx (k - r))) (isZero_zeroCx r))
      (fun i _ _ => IsZero.eq_of_src (isZero_dual (isZero_zeroCx (k - i))) _ _)), ?_⟩
    ext r
    exact IsZero.eq_of_src (isZero_dual (isZero_zeroCx (k - r))) _ _

end SymPoincare

end HSP
