import HilbertSmithPaper.LTheory.Base.Complexes.StructureInvolution
import HilbertSmithPaper.LTheory.Base.Complexes.CycleChainMap

/-!
# Strict symmetric Poincaré complex

A strict `k`-dimensional symmetric Poincaré complex in a duality category `B` is a complex `C`
whose objects `C_r` are zero objects for `r` outside `[0, k]`, with `φ ∈ M(C)_k`, `∂φ = 0`,
`T φ = φ`, such that `φ_♮ : C^{k-*} ⟶ C` is a chain homotopy equivalence.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

universe v u

/-- A *strict `k`-dimensional symmetric Poincaré complex* `(C, φ)` in a duality category `B`. -/
structure SymPoincare (B : Type u) [Category.{v} B] [Preadditive B] [Linear ℚ B]
    [HasFiniteBiproducts B] [DualCat B] (k : ℤ) where
  /-- The underlying complex. -/
  C : ChainComplex B ℤ
  /-- The structure `φ ∈ M(C)_k`. -/
  φ : (StructureCx C).X k
  /-- `C_r` is a zero object for `r` outside `[0, k]`. -/
  bounded : ∀ r : ℤ, r < 0 ∨ k < r → IsZero (C.X r)
  /-- `∂φ = 0`. -/
  cycle : (StructureCx C).d k (k - 1) φ = 0
  /-- `T φ = φ`. -/
  symmetric : (StructureCx.T C).f k φ = φ
  /-- `φ_♮ : C^{k-*} ⟶ C` is a chain homotopy equivalence. -/
  poincare : ∃ e : HomotopyEquiv (dualCx C k) C, e.hom = StructureCx.toHom φ cycle

end HSP
