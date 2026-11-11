import HilbertSmithPaper.LTheory.Localization.Products.BasedVectorSpaces
import HilbertSmithPaper.Categories.Asymptotic.FreeCategory
import HilbertSmithPaper.LTheory.Base.Categories.DualityFunctor

/-!
# Based vector spaces over the trivial group

The functor `ℚ^d ↦ ℚ[{1}]^d` from based vector spaces to `Free(ℚ[{1}])` sends a `d' × d` matrix
`u` to the equivariant matrix on the bases `{1} × {1..d}` with the same entries. With `ξ = id` it
is a strict duality functor, since both dualities are the transpose.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP.Evaluation

open FreeQ

/-- `u` on the bases `{1} × {1..d}`. -/
private def unitMatrix {m k : ℕ} (u : Matrix (Fin m) (Fin k) ℚ) :
    Matrix (Unit × Fin m) (Unit × Fin k) ℚ :=
  fun a b => u a.2 b.2

private lemma unitMatrix_mem {m k : ℕ} (u : Matrix (Fin m) (Fin k) ℚ) :
    unitMatrix u ∈ FreeCat.equivariant Unit m k :=
  fun _ _ _ _ _ => rfl

/-- The morphism of `Free(ℚ[{1}])` with the entries of `u`. -/
private def unitHom {X Y : FreeQ} (u : X ⟶ Y) :
    (⟨X.dim⟩ : FreeCat Unit) ⟶ (⟨Y.dim⟩ : FreeCat Unit) :=
  FreeCat.ofMat (unitMatrix (toMatrix u)) (unitMatrix_mem _)

private lemma unitMatrix_one (m : ℕ) :
    unitMatrix (1 : Matrix (Fin m) (Fin m) ℚ) = 1 := by
  ext ⟨⟨⟩, i⟩ ⟨⟨⟩, j⟩
  simp [unitMatrix, Matrix.one_apply]

private lemma unitMatrix_mul {l m k : ℕ} (u : Matrix (Fin l) (Fin m) ℚ)
    (v : Matrix (Fin m) (Fin k) ℚ) : unitMatrix (u * v) = unitMatrix u * unitMatrix v := by
  ext ⟨⟨⟩, i⟩ ⟨⟨⟩, j⟩
  simp [unitMatrix, Matrix.mul_apply, Fintype.sum_prod_type]

/-- The underlying functor `ℚ^d ↦ ℚ[{1}]^d`. -/
private def basedToFreeFunctor : FreeQ ⥤ FreeCat Unit where
  obj X := ⟨X.dim⟩
  map u := unitHom u
  map_id X := FreeCat.hom_ext (unitMatrix_one X.dim)
  map_comp f g := FreeCat.hom_ext (unitMatrix_mul (toMatrix g) (toMatrix f))

private instance : basedToFreeFunctor.Additive where
  map_add := FreeCat.hom_ext (by ext; rfl)

private instance : basedToFreeFunctor.Linear ℚ where
  map_smul _ _ := FreeCat.hom_ext (by ext; rfl)

/-- **Based vector spaces over the trivial group**: the duality functor `FreeQ → Free(ℚ[{1}])`,
`ℚ^d ↦ ℚ[{1}]^d`, `u ↦ u`, with `ξ = id`. -/
def basedToFree : DualFunctor FreeQ (FreeCat Unit) where
  toFunctor := basedToFreeFunctor
  ξ _ := Iso.refl _
  ξ_natural f := by
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    exact FreeCat.hom_ext (by ext; rfl)
  ξ_dual M := by
    simp only [Iso.refl_hom, eqToHom_refl, Category.comp_id]; exact DualCat.dualHom_id _

/-- `basedToFree` is a strict duality functor. -/
private theorem basedToFree_isStrict : basedToFree.IsStrict :=
  fun _ => ⟨rfl, rfl⟩

end HSP.Evaluation
