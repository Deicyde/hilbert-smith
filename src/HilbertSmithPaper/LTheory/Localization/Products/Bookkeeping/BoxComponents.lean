import Mathlib
import HilbertSmithPaper.LTheory.Localization.Products.Bookkeeping.BoxObject

/-!
# Components of box products of maps

For `f : N ⟶ N'` in `Kar B` and `g : V ⟶ V'` in `C_ℤ(ℚ)`, the component
`(f ⊠ g)_{mn} : M^{⊕ d_n} ⟶ M'^{⊕ d'_m}` is the block matrix whose `(i, i')` entry (from summand
`i` to summand `i'`) is `(g_{mn})_{i'i} f`.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents

namespace HSP

universe v u

variable {B : Type u} [Category.{v} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]

namespace Box

/-- **Components of box products of maps.** The components `(f ⊠ g)_{mn}`: block matrices with
entries `(g_{mn})_{i'i} f`. -/
noncomputable def F {N N' : Karoubi B} {V V' : Bounded FreeQ} (f : N ⟶ N') (g : V ⟶ V')
    (m n : ℤ) : (obj N V).X.X n ⟶ (obj N' V').X.X m :=
  biproduct.matrix fun (i : Fin (V.X n).dim) (i' : Fin (V'.X m).dim) =>
    FreeQ.toMatrix (g.1 m n) i' i • f.f

@[reassoc]
lemma F_entry {N N' : Karoubi B} {V V' : Bounded FreeQ} (f : N ⟶ N') (g : V ⟶ V') (m n : ℤ)
    (i : Fin (V.X n).dim) (i' : Fin (V'.X m).dim) :
    biproduct.ι (fun _ : Fin (V.X n).dim => N.X) i ≫ F f g m n ≫
        biproduct.π (fun _ : Fin (V'.X m).dim => N'.X) i' =
      FreeQ.toMatrix (g.1 m n) i' i • f.f :=
  biproduct.matrix_components _ _ _

end Box

end HSP
