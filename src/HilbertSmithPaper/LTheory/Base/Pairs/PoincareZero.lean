import HilbertSmithPaper.LTheory.Base.Pairs.SymmetricPoincareComplex

/-!
# Zero Poincaré complex

The zero complex with the zero structure, `(0, 0)`, is a strict `k`-dimensional symmetric Poincaré
complex: all chain objects of `0` and `0^{k-*}` are zero objects, so `0_♮` is an isomorphism.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

open DualCat

universe v u

variable {B : Type u} [Category.{v} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B]

namespace SymPoincare

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
