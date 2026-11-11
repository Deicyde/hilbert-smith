import Mathlib
import HilbertSmithPaper.LTheory.Localization.Products.BasedVectorSpaces

/-!
# Realization of based complexes

The based vector space `ℚ^d` is realized as the `ℚ`-module of functions `Fin d → ℚ`, with its
standard basis, and a `d' × d` matrix as multiplication of columns by it. This is an additive
functor, so it applies degreewise to chain complexes; the basis vector `e_a` of `ℚ^d` is the
`a`-th standard basis vector, and the coefficient of `e_b` in `f(e_a)` is the entry `f_{ba}`.

## Encoding

* `realization : FreeQ ⥤ ModuleCat ℚ` (the declaration of the article) sends `⟨d⟩` to
  `ModuleCat.of ℚ (Fin d → ℚ)` and a matrix `A` to `Matrix.mulVecLin A`; it is additive.
* `realizeCx C` is its application to a complex `C : ChainComplex FreeQ ℤ`
  (`Functor.mapHomologicalComplex`), and `realizeBasis C r` the standard basis of
  `(realizeCx C)_r`, indexed by the basis `Fin (C.X r).dim` of `C_r`.
* `realizeCx_d_apply`, `realizeBasis_repr` and `realizeBasis_repr_d` give the compatibility: the
  differential acts by `mulVec`, coordinates in the standard basis are the entries of the
  column, and the coefficient of `e_b` in `d(e_a)` is the matrix entry.
-/

open CategoryTheory

namespace HSP.ChainModels

open FreeQ Matrix

/-- The realization of a based vector space `ℚ^d`: the module of functions `Fin d → ℚ`. -/
abbrev realizeObj (X : FreeQ) : ModuleCat.{0} ℚ := ModuleCat.of ℚ (Fin X.dim → ℚ)

/-- The *realization* functor from based vector spaces to `ℚ`-modules: `ℚ^d` is realized as
`Fin d → ℚ` and a matrix as multiplication of columns by it. -/
noncomputable def realization : FreeQ ⥤ ModuleCat.{0} ℚ where
  obj X := realizeObj X
  map f := ModuleCat.ofHom (Matrix.mulVecLin (toMatrix f))
  map_id X := by
    ext : 1
    simp
  map_comp f g := by
    ext : 1
    simp [Matrix.mulVecLin_mul]

lemma realization_map_apply {X Y : FreeQ} (f : X ⟶ Y) (z : Fin X.dim → ℚ) :
    (realization.map f).hom z = toMatrix f *ᵥ z := rfl

instance : realization.Additive where
  map_add {X Y f g} := by
    ext : 1
    simp only [realization]
    exact (Matrix.mulVecLin_add _ _).trans rfl

/-- The realization of a complex of based vector spaces, degreewise. -/
noncomputable abbrev realizeCx (C : ChainComplex FreeQ ℤ) : ChainComplex (ModuleCat.{0} ℚ) ℤ :=
  (realization.mapHomologicalComplex (ComplexShape.down ℤ)).obj C

/-- The standard basis of `(realizeCx C)_r`, indexed by the basis of `C_r`. -/
noncomputable def realizeBasis (C : ChainComplex FreeQ ℤ) (r : ℤ) :
    Module.Basis (Fin (C.X r).dim) ℚ ((realizeCx C).X r) :=
  Pi.basisFun ℚ (Fin (C.X r).dim)

lemma realizeCx_d_apply (C : ChainComplex FreeQ ℤ) (r s : ℤ) (z : Fin (C.X r).dim → ℚ) :
    ((realizeCx C).d r s).hom z = toMatrix (C.d r s) *ᵥ z := rfl

lemma realizeBasis_apply (C : ChainComplex FreeQ ℤ) (r : ℤ) (a : Fin (C.X r).dim) :
    realizeBasis C r a = Pi.single a 1 := by
  exact Pi.basisFun_apply ℚ (Fin (C.X r).dim) a

lemma realizeBasis_repr (C : ChainComplex FreeQ ℤ) (r : ℤ) (z : (realizeCx C).X r)
    (a : Fin (C.X r).dim) : (realizeBasis C r).repr z a = (show Fin (C.X r).dim → ℚ from z) a := by
  exact Pi.basisFun_repr ℚ (Fin (C.X r).dim) z a

/-- The coefficient of `e_b` in `d(e_a)` is the matrix entry `d_{ba}`. -/
lemma realizeBasis_repr_d (C : ChainComplex FreeQ ℤ) (r s : ℤ) (a : Fin (C.X r).dim)
    (b : Fin (C.X s).dim) :
    (realizeBasis C s).repr (((realizeCx C).d r s).hom (realizeBasis C r a)) b =
      toMatrix (C.d r s) b a := by
  rw [realizeBasis_repr, realizeBasis_apply, realizeCx_d_apply]
  simp [Matrix.mulVec_single]

end HSP.ChainModels
