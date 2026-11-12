import Mathlib
import HilbertSmithPaper.Signatures.Real.RealCohomology

/-!
# The action of `G` on real cohomology

`G` acts on `ℝ^{G × Fin n}` by permuting the basis, `a (g, k) = (a + g, k)`, that is
`(a · v)(g, k) = v(-a + g, k)`. Equivariant matrices commute with this action, so it preserves the
real cocycles and coboundaries and induces a representation of `G` on `H^r(C; ℝ)`
(`HSP.realHco.rep`). Since `G` is written additively, this is a representation of
`Multiplicative G`.
-/

open CategoryTheory CategoryTheory.Idempotents

namespace HSP

open DualCat FreeCat

variable {G : Type} [AddGroup G] [Fintype G]

/-- The permutation representation `(a · v)(g, k) = v(-a + g, k)` on `ℝ^{G × Fin n}`. -/
private noncomputable def permRep (n : ℕ) :
    Representation ℝ (Multiplicative G) (G × Fin n → ℝ) where
  toFun a := LinearMap.funLeft ℝ ℝ fun b : G × Fin n => (-Multiplicative.toAdd a + b.1, b.2)
  map_one' := by
    ext v b
    simp [LinearMap.funLeft]
  map_mul' a b := by
    ext v x
    simp [LinearMap.funLeft, neg_add_rev, add_assoc]

/-- Equivariant matrices commute with the permutation action. -/
private theorem realMap_permRep {M N : FreeCat G} (u : M ⟶ N) (a : Multiplicative G)
    (v : G × Fin M.n → ℝ) : realMap u (permRep M.n a v) = permRep N.n a (realMap u v) := by
  funext x
  simp only [realMap_apply, permRep, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.funLeft_apply,
    Matrix.mulVec, dotProduct, Matrix.map_apply]
  refine Fintype.sum_equiv
    ((Equiv.addLeft (-Multiplicative.toAdd a)).prodCongr (Equiv.refl _)) _ _ fun b => ?_
  simp only [Equiv.prodCongr_apply, Equiv.coe_addLeft, Equiv.coe_refl]
  congr 2
  have h := u.2 (Multiplicative.toAdd a) (-Multiplicative.toAdd a + x.1)
    (-Multiplicative.toAdd a + b.1) x.2 b.2
  simp only [add_neg_cancel_left] at h
  exact h

variable [DecidableEq G] {C : ChainComplex (Karoubi (FreeCat G)) ℤ} {r : ℤ}

/-- **The action of `G` on `H^r(C; ℝ)`** by permuting the basis. -/
noncomputable def realHco.rep : Representation ℝ (Multiplicative G) (realHco C r) where
  toFun a := Submodule.mapQ _ _ ((permRep _ a).restrict fun x hx => by
      obtain ⟨⟨w, hw⟩, hk⟩ := hx
      exact ⟨⟨permRep _ a w, by rw [realMap_permRep, hw]⟩,
        LinearMap.mem_ker.2 (by rw [realMap_permRep, LinearMap.mem_ker.1 hk, map_zero])⟩)
    fun x hx => by
      obtain ⟨y, ⟨w, hw⟩, hy⟩ := hx
      exact ⟨permRep _ a y, ⟨permRep _ a w, by rw [realMap_permRep, hw]⟩,
        by rw [realMap_permRep, hy]; rfl⟩
  map_one' := by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun x => ?_)
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply,
      LinearMap.restrict_apply, map_one, Module.End.one_apply]
  map_mul' a b := by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun x => ?_)
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply,
      LinearMap.restrict_apply, map_mul, Module.End.mul_apply]

end HSP
