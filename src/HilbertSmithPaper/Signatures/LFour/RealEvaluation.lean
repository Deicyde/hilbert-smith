import Mathlib
import HilbertSmithPaper.Signatures.LFour.RealHomology

/-!
# The evaluation pairing

For a chain complex `C` in `Kar Free(ℚ[G])`, the evaluation pairing
`⟨-, -⟩ : H^r(C; ℝ) × H_r(C; ℝ) → ℝ` is `⟨[x], [y]⟩ = Σ_b x_b y_b` for a real cocycle `x` and a
real cycle `y` (`HSP.realEval`, a bilinear map, `HSP.realEval_mk`).

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

/-- The dot product of a real cocycle and a real cycle. -/
private noncomputable def evalAux : realCocycles C r →ₗ[ℝ] realCycles C r →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => (x : G × Fin (C.X r).X.n → ℝ) ⬝ᵥ (y : G × Fin (C.X r).X.n → ℝ))
    (fun _ _ _ => add_dotProduct _ _ _) (fun _ _ _ => smul_dotProduct _ _ _)
    (fun _ _ _ => dotProduct_add _ _ _) (fun _ _ _ => dotProduct_smul _ _ _)

private theorem evalAux_boundary (x : realCocycles C r) :
    (realBoundaries C r).comap (realCycles C r).subtype ≤ LinearMap.ker (evalAux C r x) := by
  rintro y ⟨z, -, hz⟩
  rw [LinearMap.mem_ker]
  change (x : G × Fin (C.X r).X.n → ℝ) ⬝ᵥ (y : G × Fin (C.X r).X.n → ℝ) = 0
  rw [show (y : G × Fin (C.X r).X.n → ℝ) = _ from hz.symm, ← dot_dualHom]
  change realMap (dualHom (C.d (r + 1) r)).f x ⬝ᵥ z = 0
  rw [LinearMap.mem_ker.1 x.2.2, zero_dotProduct]

/-- The pairing of a cocycle with homology classes. -/
private noncomputable def evalAux' : realCocycles C r →ₗ[ℝ] realH C r →ₗ[ℝ] ℝ where
  toFun x := Submodule.liftQ _ (evalAux C r x) (evalAux_boundary C r x)
  map_add' x x' := Submodule.linearMap_qext _ (LinearMap.ext fun y => by
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.liftQ_apply, map_add,
      LinearMap.add_apply])
  map_smul' c x := Submodule.linearMap_qext _ (LinearMap.ext fun y => by
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.liftQ_apply, map_smul,
      LinearMap.smul_apply, RingHom.id_apply])

private theorem evalAux'_coboundary :
    (realCoboundaries C r).comap (realCocycles C r).subtype ≤ LinearMap.ker (evalAux' C r) := by
  rintro x ⟨w, -, hw⟩
  rw [LinearMap.mem_ker]
  refine Submodule.linearMap_qext _ (LinearMap.ext fun y => ?_)
  change (x : G × Fin (C.X r).X.n → ℝ) ⬝ᵥ (y : G × Fin (C.X r).X.n → ℝ) = 0
  rw [show (x : G × Fin (C.X r).X.n → ℝ) = _ from hw.symm]
  change realMap (dualHom (C.d r (r - 1)).f) w ⬝ᵥ y = 0
  rw [dot_dualHom, LinearMap.mem_ker.1 y.2.2, dotProduct_zero]

/-- **The evaluation pairing** `⟨-, -⟩ : H^r(C; ℝ) × H_r(C; ℝ) → ℝ`, `⟨[x], [y]⟩ = Σ_b x_b y_b`. -/
noncomputable def realEval : realHco C r →ₗ[ℝ] realH C r →ₗ[ℝ] ℝ :=
  Submodule.liftQ _ (evalAux' C r) (evalAux'_coboundary C r)

theorem realEval_mk (x : realCocycles C r) (y : realCycles C r) :
    realEval C r (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) =
      (x : G × Fin (C.X r).X.n → ℝ) ⬝ᵥ (y : G × Fin (C.X r).X.n → ℝ) := rfl

end HSP
