import Mathlib
import HilbertSmithPaper.Signatures.Real.RealCohomology

/-!
# The map on real cohomology induced by a chain map

A chain map `f : C ⟶ D` of complexes in `Kar Free(ℚ[G])` induces
`f^* : H^r(D; ℝ) → H^r(C; ℝ)`, `[x] ↦ [f_rᵀ x]` (`HSP.realHco.map`): the transposed matrices
`f_rᵀ` map real cochains to real cochains (`f_r = e'_r f_r e_r`), and they commute with the
coboundaries because `f` commutes with the differentials.
-/

open CategoryTheory CategoryTheory.Idempotents

namespace HSP

open DualCat FreeCat

variable {G : Type} [AddGroup G] [Fintype G] [DecidableEq G]

private theorem realMap_comp_apply {M N P : FreeCat G} (u : M ⟶ N) (v : N ⟶ P)
    (w : G × Fin M.n → ℝ) : realMap (u ≫ v) w = realMap v (realMap u w) := by
  simp only [realMap_apply, mat_comp, Matrix.map_mul, Matrix.mulVec_mulVec]

variable {C D : ChainComplex (Karoubi (FreeCat G)) ℤ} {r : ℤ}

/-- **The map `f^* : H^r(D; ℝ) → H^r(C; ℝ)`** induced by a chain map, `[x] ↦ [f_rᵀ x]`. -/
noncomputable def realHco.map (f : C ⟶ D) : realHco D r →ₗ[ℝ] realHco C r :=
  Submodule.mapQ _ _ ((realMap (dualHom (f.f r)).f).restrict fun x hx => by
      have h := congrArg (fun h : C.X (r + 1) ⟶ D.X r => realMap (dualHom h).f x)
        (f.comm (r + 1) r)
      simp only [dualHom_comp, Karoubi.comp_f, realMap_comp_apply] at h
      refine ⟨⟨realMap (dualHom (f.f r)).f x, ?_⟩, LinearMap.mem_ker.2 ?_⟩
      · rw [← realMap_comp_apply, Karoubi.comp_p]
      · rw [← h, LinearMap.mem_ker.1 hx.2, map_zero])
    fun x hx => by
      obtain ⟨y, -, hy⟩ := hx
      have h := congrArg (fun h : C.X r ⟶ D.X (r - 1) => realMap (dualHom h).f y)
        (f.comm r (r - 1))
      simp only [dualHom_comp, Karoubi.comp_f, realMap_comp_apply] at h
      refine ⟨realMap (dualHom (f.f (r - 1))).f y, ⟨realMap (dualHom (f.f (r - 1))).f y, ?_⟩, ?_⟩
      · rw [← realMap_comp_apply, Karoubi.comp_p]
      · rw [← h, hy]; rfl

end HSP
