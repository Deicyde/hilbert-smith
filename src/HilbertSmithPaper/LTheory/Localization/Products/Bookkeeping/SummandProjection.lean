import Mathlib
import HilbertSmithPaper.LTheory.Localization.Products.ComplexProduct

/-!
# Summand projections of a tensor product

For a duality pairing `(⊠, κ)` and complexes `C`, `D` with finitely many nonzero chain objects,
the projection `π_{p,q} : (C ⊗ D)_r → C_p ⊠ D_q` onto a summand when `p + q = r`, and `0`
otherwise. It is the map out of the direct sum that is the identity on the summand `(p, q)` and
zero on the other summands.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {B : Type u₁} [Category.{v₁} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B]
  {E : Type u₂} [Category.{v₂} E] [Preadditive E] [Linear ℚ E] [HasFiniteBiproducts E]
  [DualCat E]
  {B'' : Type u₃} [Category.{v₃} B''] [Preadditive B''] [Linear ℚ B''] [HasFiniteBiproducts B'']
  [DualCat B'']
  (P : DualityPairing B E B'')

namespace cxProd

variable {C : ChainComplex B ℤ} {D : ChainComplex E ℤ}
  (hC : {r | ¬ IsZero (C.X r)}.Finite) (hD : {r | ¬ IsZero (D.X r)}.Finite)

/-- **Summand projections of a tensor product.** The projection of `(C ⊗ D)_r` onto the summand
`C_p ⊠ D_q` (zero unless `p + q = r`). -/
noncomputable def π (p q r : ℤ) : (cxProd P C D hC hD).X r ⟶ P.tensor.obj (C.X p, D.X q) :=
  haveI := P.hasMapBifunctor_of_finite hC hD
  HomologicalComplex.mapBifunctorDesc (K₁ := C) (K₂ := D) (F := Functor.curry.obj P.tensor)
    (c := ComplexShape.down ℤ) (j := r) fun p' q' _ =>
      if h : p' = p ∧ q' = q then eqToHom (by obtain ⟨rfl, rfl⟩ := h; rfl) else 0

end cxProd

end HSP
