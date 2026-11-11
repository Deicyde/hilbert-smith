import HilbertSmithPaper.LTheory.Base.Complexes.Functors.DualMap

/-!
# Duals of chain maps reverse composition

`(f ≫ g)^{n-*} = g^{n-*} ≫ f^{n-*}`, componentwise from `(g f)^* = f^* g^*`.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

open DualCat

universe v u

variable {B : Type u} [Category.{v} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B]

/-- **Duals of chain maps reverse composition.** `(f ≫ g)^{n-*} = g^{n-*} ≫ f^{n-*}`. -/
lemma dualCx.map_comp {C D E : ChainComplex B ℤ} (f : C ⟶ D) (g : D ⟶ E) (n : ℤ) :
    dualCx.map (f ≫ g) n = dualCx.map g n ≫ dualCx.map f n := by
  ext r
  simp

end HSP
