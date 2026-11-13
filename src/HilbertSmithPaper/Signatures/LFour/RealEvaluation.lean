import Mathlib
import HilbertSmithPaper.Signatures.LFour.RealHomology
import HilbertSmithPaper.Signatures.Real.RealCohomology

/-!
# The evaluation pairing

For a chain complex `C` in `Kar Free(ℚ[G])`, the evaluation pairing
`⟨-, -⟩ : H^r(C; ℝ) × H_r(C; ℝ) → ℝ` is `⟨[x], [y]⟩ = Σ_b x_b y_b` for a real cocycle `x` and a
real cycle `y` (`HSP.realEval`, a bilinear map, with defining equation `HSP.realEval_mk`).

Well-definedness: `⟨dᵀ w, y⟩ = ⟨w, d y⟩ = 0` for a cycle `y`, and `⟨x, d z⟩ = ⟨dᵀ x, z⟩ = 0` for a
cocycle `x`. Lean encoding: the dot product on cocycles × cycles, descended through both quotients
with `Submodule.liftQ`.
-/

open CategoryTheory CategoryTheory.Idempotents

namespace HSP

open DualCat FreeCat

variable {G : Type} [AddGroup G] [Fintype G] [DecidableEq G]
  (C : ChainComplex (Karoubi (FreeCat G)) ℤ) (r : ℤ)

/-- `⟨uᵀ x, y⟩ = ⟨x, u y⟩` for the real matrices. -/
private theorem dot_dualHom {M N : FreeCat G} (u : M ⟶ N) (x : G × Fin N.n → ℝ)
    (y : G × Fin M.n → ℝ) : realMap (dualHom u) x ⬝ᵥ y = x ⬝ᵥ realMap u y := by
  rw [realMap_apply, realMap_apply, mat_dualHom, Matrix.transpose_map, Matrix.mulVec_transpose,
    Matrix.dotProduct_mulVec]

/-- The dot product on `ℝ^{G × Fin n}` as a bilinear map. -/
private noncomputable def dotBil (n : ℕ) : (G × Fin n → ℝ) →ₗ[ℝ] (G × Fin n → ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ dotProduct (fun _ _ _ => add_dotProduct _ _ _)
    (fun _ _ _ => smul_dotProduct _ _ _) (fun _ _ _ => dotProduct_add _ _ _)
    (fun _ _ _ => dotProduct_smul _ _ _)

/-- **The evaluation pairing** `⟨-, -⟩ : H^r(C; ℝ) × H_r(C; ℝ) → ℝ`, `⟨[x], [y]⟩ = Σ_b x_b y_b`. -/
noncomputable def realEval : realHco C r →ₗ[ℝ] realH C r →ₗ[ℝ] ℝ :=
  Submodule.liftQ _
    { toFun := fun x => Submodule.liftQ _ ((dotBil _ x.1).comp (Submodule.subtype _)) (by
        rintro y ⟨z, -, hz⟩
        rw [LinearMap.mem_ker]
        change x.1 ⬝ᵥ y.1 = 0
        rw [show y.1 = _ from hz.symm, ← dot_dualHom]
        change realMap (dualHom (C.d (r + 1) r)).f x.1 ⬝ᵥ z = 0
        rw [LinearMap.mem_ker.1 x.2.2, zero_dotProduct])
      map_add' := fun x x' => Submodule.linearMap_qext _ (LinearMap.ext fun y =>
        add_dotProduct x.1 x'.1 y.1)
      map_smul' := fun c x => Submodule.linearMap_qext _ (LinearMap.ext fun y =>
        smul_dotProduct c x.1 y.1) }
    (by
      rintro x ⟨w, -, hw⟩
      rw [LinearMap.mem_ker]
      refine Submodule.linearMap_qext _ (LinearMap.ext fun y => ?_)
      change x.1 ⬝ᵥ y.1 = 0
      rw [show x.1 = _ from hw.symm]
      change realMap (dualHom (C.d r (r - 1)).f) w ⬝ᵥ y.1 = 0
      rw [dot_dualHom, LinearMap.mem_ker.1 y.2.2, dotProduct_zero])

private theorem realEval_mk (x y) :
    realEval C r (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) = x.1 ⬝ᵥ y.1 := rfl

end HSP
