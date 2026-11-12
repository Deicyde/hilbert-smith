import HilbertSmithPaper.LTheory.Base.Pairs.SymmetricPoincareComplex

/-!
# Negative of a Poincaré complex

The negative `(C, -φ)` of a strict `k`-dimensional symmetric Poincaré complex `(C, φ)` is a strict
`k`-dimensional symmetric Poincaré complex: `(-φ)_♮ = -φ_♮`, and negating an equivalence, its
inverse and its homotopies gives an equivalence.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

open DualCat

universe v u

variable {B : Type u} [Category.{v} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B]

namespace SymPoincare

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

end SymPoincare

end HSP
