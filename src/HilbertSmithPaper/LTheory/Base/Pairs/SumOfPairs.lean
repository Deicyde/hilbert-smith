import HilbertSmithPaper.LTheory.Base.Pairs.PoincarePair
import HilbertSmithPaper.LTheory.Base.Complexes.SumOfComplexes

/-!
# Sums of pairs

If `(f : C ⟶ D, δφ, φ)` and `(f' : C' ⟶ D', δφ', φ')` are strict `n`-dimensional Poincaré
pairs, then so is `(f ⊕ f' : C ⊞ C' ⟶ D ⊞ D', δφ ⊕ δφ', φ ⊕ φ')`.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

open DualCat

universe v u

variable {B : Type u} [Category.{v} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B]

/-- The sum of two strict `n`-dimensional Poincaré pairs is a strict `n`-dimensional
Poincaré pair. -/
theorem SymPair.sum {m n : ℤ} (W W' : SymPair B m n) :
    ∃ W'' : SymPair B m n, W''.data = ⟨W.C ⊞ W'.C, W.D ⊞ W'.D, biprod.map W.f W'.f,
      StructureCx.sum W.δφ W'.δφ, StructureCx.sum W.φ W'.φ⟩ := by
  sorry

end HSP
