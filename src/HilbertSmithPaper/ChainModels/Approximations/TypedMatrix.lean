import Mathlib
import HilbertSmithPaper.ChainModels.Grid.Torus

/-!
# Typed labelled matrices

A *typed labelled matrix* (`TypedMatrix n p`) is a matrix `u : ℚ^B → ℚ^{B'}` between finite
sets of cells with torus labels `x`, `x'`, together with its type `c ∈ C_p`.
-/

namespace HSP.ChainModels

variable {p : ℕ} [Fact p.Prime] {n : ℕ}

/-- A matrix `u : ℚ^B → ℚ^{B'}` between finite sets of cells with torus labels, with a type
`c ∈ C_p`. -/
structure TypedMatrix (n p : ℕ) where
  /-- The source cells. -/
  B : Type
  /-- The target cells. -/
  B' : Type
  [fintypeB : Fintype B]
  [fintypeB' : Fintype B']
  /-- The torus labels of the source cells. -/
  x : B → Torus n
  /-- The torus labels of the target cells. -/
  x' : B' → Torus n
  /-- The matrix. -/
  u : Matrix B' B ℚ
  /-- The type. -/
  c : ZMod p

attribute [instance] TypedMatrix.fintypeB TypedMatrix.fintypeB'

/-- The typed matrix `u` of type `c`, with source labels `x` and target labels `x'`. -/
def TypedMatrix.of {B B' : Type} [Fintype B] [Fintype B'] (x : B → Torus n) (x' : B' → Torus n)
    (u : Matrix B' B ℚ) (c : ZMod p) : TypedMatrix n p :=
  { B := B, B' := B', x := x, x' := x', u := u, c := c }

end HSP.ChainModels
