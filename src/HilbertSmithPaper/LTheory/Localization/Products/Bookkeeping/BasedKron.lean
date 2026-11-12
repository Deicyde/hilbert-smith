import Mathlib
import HilbertSmithPaper.LTheory.Localization.Products.Bookkeeping.BasedCategory

/-!
# Kronecker product of matrices

For morphisms `f : ℚ^a → ℚ^{a'}` and `g : ℚ^b → ℚ^{b'}` of based vector spaces, the morphism
`ℚ^{ab} → ℚ^{a'b'}` given by the Kronecker product `f ⊗ₖ g`, reindexed on rows and columns along
`finProdFinEquiv`, which sends `(i, j)` to `b * i + j` (0-based): its entry in row `(i, j)` and
column `(k, l)` is `f i k * g j l`.
-/

open CategoryTheory
open scoped Kronecker

namespace HSP

open FreeQ

/-- **Kronecker product of matrices.** The Kronecker product of two morphisms of `ℚ`,
reindexed along `finProdFinEquiv`. -/
def basedKron {X X' Y Y' : FreeQ} (f : X ⟶ X') (g : Y ⟶ Y') :
    (⟨X.dim * Y.dim⟩ : FreeQ) ⟶ ⟨X'.dim * Y'.dim⟩ :=
  ofMatrix ((toMatrix f ⊗ₖ toMatrix g).submatrix finProdFinEquiv.symm finProdFinEquiv.symm)

end HSP
