import HilbertSmithPaper.LTheory.Base.Complexes.Cone

/-!
# The shift of a complex

The shift of a complex `C` is the mapping cone of `C ⟶ 0`: `(Σ C)_r = 0 ⊞ C_{r-1}`, with the
differential of `C` on the second summand.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

universe v u

variable {V : Type u} [Category.{v} V] [Preadditive V] [HasBinaryBiproducts V]

open ZeroObject in
/-- **The shift of a complex.** `Σ C = 𝒞(C ⟶ 0)`: `(Σ C)_r = 0 ⊞ C_{r-1}` with differential `d`
on `C_{r-1}`. -/
noncomputable abbrev cone.shift [HasZeroObject V] (C : ChainComplex V ℤ) : ChainComplex V ℤ :=
  cone (0 : C ⟶ 0)

end HSP
