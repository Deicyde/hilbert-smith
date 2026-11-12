import Mathlib
import HilbertSmithPaper.LTheory.Localization.Products.BasedVectorSpaces
import HilbertSmithPaper.LTheory.Base.Categories.KaroubiDuality
import HilbertSmithPaper.LTheory.Bounded.Categories.IteratedBoundedCategory
import HilbertSmithPaper.LTheory.Bounded.Categories.BoundedDiag

/-!
# Objects of the box product

For a ℚ-linear additive category `B`, `N = (M, e)` in `Kar B` and `V = (ℚ^{d_n})_n` in
`C_ℤ(ℚ)`, the object `N ⊠ V` of `Kar C_ℤ(B)` has `M^{⊕ d_n}` in position `n` (the biproduct of
`d_n` copies of `M`) and the idempotent `e` on each summand.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents

namespace HSP

universe v u

variable {B : Type u} [Category.{v} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]

namespace Box

omit [Linear ℚ B] in
private lemma biprod_ext {J K : Type} [Fintype J] [Fintype K] {f : J → B} {g : K → B}
    {φ ψ : ⨁ f ⟶ ⨁ g}
    (h : ∀ j k, biproduct.ι f j ≫ φ ≫ biproduct.π g k = biproduct.ι f j ≫ ψ ≫ biproduct.π g k) :
    φ = ψ := by
  refine biproduct.hom_ext' _ _ fun j => biproduct.hom_ext _ _ fun k => ?_
  simpa only [Category.assoc] using h j k

/-- **Objects of the box product.** The object `N ⊠ V`: `M^{⊕ d_n}` in position `n`, with `e`
on each summand. -/
noncomputable abbrev obj (N : Karoubi B) (V : Bounded FreeQ) : Karoubi (Bounded B) where
  X := ⟨fun n => ⨁ fun _ : Fin (V.X n).dim => N.X⟩
  p := Bounded.diag fun n => biproduct.map fun _ => N.p
  idem := by
    rw [Bounded.diag_comp_diag]
    congr 1
    funext n
    exact biprod_ext fun i i' => by simp

end Box

end HSP
