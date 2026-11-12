import Mathlib
import HilbertSmithPaper.Categories.Asymptotic.FreeCategory

/-!
# The real matrix of a morphism

A morphism `u : M ⟶ N` of `Free(ℚ[G])` is an equivariant rational matrix with rows indexed by
`G × Fin N.n` and columns by `G × Fin M.n`. Its real matrix acts on real vectors,
`ℝ^{G × Fin M.n} → ℝ^{G × Fin N.n}`, `v ↦ u v` (`HSP.FreeCat.realMap`, `HSP.FreeCat.realMap_apply`),
with the entries cast from `ℚ` to `ℝ`.
-/

namespace HSP

namespace FreeCat

variable {G : Type} [AddGroup G] [Fintype G]

/-- The real matrix of `u : M ⟶ N`, acting on real vectors, `ℝ^{G × Fin M.n} → ℝ^{G × Fin N.n}`. -/
noncomputable def realMap {M N : FreeCat G} (u : M ⟶ N) :
    (G × Fin M.n → ℝ) →ₗ[ℝ] (G × Fin N.n → ℝ) :=
  ((mat u).map (Rat.castHom ℝ)).mulVecLin

theorem realMap_apply {M N : FreeCat G} (u : M ⟶ N) (v : G × Fin M.n → ℝ) :
    realMap u v = ((mat u).map (Rat.castHom ℝ)).mulVec v := rfl

end FreeCat

end HSP
