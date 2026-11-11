import HilbertSmithPaper.LTheory.Base.Pairs.PoincarePair
import HilbertSmithPaper.LTheory.Base.Complexes.SumOfComplexes

/-!
# Cobordism

Strict `k`-dimensional symmetric Poincaré complexes `(C, φ)` and `(C', φ')` are *cobordant* if
there is a strict `(k+1)`-dimensional Poincaré pair with boundary `(C ⊕ C', φ ⊕ (-φ'))`.

Lean: the boundary of the pair `W` equals `(C ⊞ C', φ ⊕ (-φ'))` as an element of the type of
structured complexes `Σ C, M(C)_k`.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

universe v u

variable {B : Type u} [Category.{v} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B]

/-- `(C, φ)` and `(C', φ')` are *cobordant* if some strict `(k+1)`-dimensional Poincaré pair has
boundary `(C ⊞ C', φ ⊕ (-φ'))`. -/
def Cobordant {k : ℤ} (x y : SymPoincare B k) : Prop :=
  ∃ W : SymPair B k (k + 1),
    (⟨W.C, W.φ⟩ : Σ C : ChainComplex B ℤ, (StructureCx C).X k) =
      ⟨x.C ⊞ y.C, StructureCx.sum x.φ (-y.φ)⟩

end HSP
