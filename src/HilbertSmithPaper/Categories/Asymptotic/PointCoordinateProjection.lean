import Mathlib
import HilbertSmithPaper.Categories.Asymptotic.PointSequenceCategory

/-!
# Coordinate projection of the sequence category

For a group sequence `𝐆` and `i ∈ ℕ`, the coordinate projection `π_i : 𝒫_𝐆 → Free(ℚ[G_i])`
sends `(n_j)` to `n_i` and `(u_j)` to `u_i`; it is a duality functor with `ξ = id`, so it is
strict.

## Encoding

`PCat.proj G i` (the declaration of the article) is a `DualFunctor` whose underlying functor is
the private `projFunctor`, which is additive and `ℚ`-linear.
-/

open CategoryTheory

namespace HSP.PCat

variable {p : ℕ} {G : GroupSeq p}

/-- The coordinate functor `π_i : 𝒫_𝐆 → Free(ℚ[G_i])`. -/
private def projFunctor (G : GroupSeq p) (i : ℕ) : PCat G ⥤ FreeCat (G.G i) where
  obj X := X.coord i
  map f := homCoord f i

private instance (i : ℕ) : (projFunctor G i).Additive where
private instance (i : ℕ) : (projFunctor G i).Linear ℚ where

/-- The *coordinate projection* `π_i : 𝒫_𝐆 → Free(ℚ[G_i])`, a duality functor with `ξ = id`. -/
def proj (G : GroupSeq p) (i : ℕ) : DualFunctor (PCat G) (FreeCat (G.G i)) where
  toFunctor := projFunctor G i
  ξ _ := Iso.refl _
  ξ_natural f := by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]; rfl
  ξ_dual M := by
    simp only [Iso.refl_hom, eqToHom_refl, Category.comp_id]; exact DualCat.dualHom_id _

end HSP.PCat
