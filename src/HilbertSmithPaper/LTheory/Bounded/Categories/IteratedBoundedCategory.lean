import HilbertSmithPaper.LTheory.Bounded.Categories.BoundedDuality

/-!
# Iterated bounded categories

`C_{ℤ^0}(A) = A` and `C_{ℤ^{j+1}}(A) = C_ℤ(C_{ℤ^j}(A))`, with the induced duality at each step.

Encoding: the recursion runs on a private bundle of a type with its category, preadditive,
ℚ-linear, finite-biproduct and duality structures, so that each level carries its instances.
`BoundedPow A j` is the underlying type; `BoundedPow A (j + 1)` is definitionally
`Bounded (BoundedPow A j)` (`boundedPow_succ`), with the same instances, and `BoundedPow A 0` is
definitionally `A`. The new coordinate is the outermost one.
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace HSP

universe v u

/-- A duality category bundled with its structure (private encoding of the recursion). -/
private structure DualBundle where
  C : Type u
  [cat : Category.{v} C]
  [pre : Preadditive C]
  [lin : Linear ℚ C]
  [bip : HasFiniteBiproducts C]
  [dc : DualCat C]

attribute [instance] DualBundle.cat DualBundle.pre DualBundle.lin DualBundle.bip DualBundle.dc

variable (A : Type u) [Category.{v} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A]

/-- The bundle of `C_{ℤ^j}(A)`, by recursion on `j`. -/
private def boundedPowBundle : ℕ → DualBundle.{v, u}
  | 0 => ⟨A⟩
  | j + 1 => ⟨Bounded (boundedPowBundle j).C⟩

/-- The iterated bounded category `C_{ℤ^j}(A)`: `C_{ℤ^0}(A) = A` and
`C_{ℤ^{j+1}}(A) = C_ℤ(C_{ℤ^j}(A))`, with the induced duality at each step. -/
def BoundedPow (j : ℕ) : Type u := (boundedPowBundle A j).C

namespace BoundedPow

variable (j : ℕ)

instance : Category.{v} (BoundedPow A j) := (boundedPowBundle A j).cat
instance : Preadditive (BoundedPow A j) := (boundedPowBundle A j).pre
instance : Linear ℚ (BoundedPow A j) := (boundedPowBundle A j).lin
instance : HasFiniteBiproducts (BoundedPow A j) := (boundedPowBundle A j).bip
instance : DualCat (BoundedPow A j) := (boundedPowBundle A j).dc

end BoundedPow

/-- `C_{ℤ^0}(A) = A`. -/
private lemma boundedPow_zero : BoundedPow A 0 = A := rfl

/-- `C_{ℤ^{j+1}}(A) = C_ℤ(C_{ℤ^j}(A))`. -/
private lemma boundedPow_succ (j : ℕ) : BoundedPow A (j + 1) = Bounded (BoundedPow A j) := rfl

end HSP

end
