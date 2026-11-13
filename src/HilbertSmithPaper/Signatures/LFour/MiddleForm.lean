import Mathlib
import HilbertSmithPaper.Signatures.LFour.RealEvaluation
import HilbertSmithPaper.LTheory.Base.Categories.KaroubiDuality
import HilbertSmithPaper.LTheory.Base.Pairs.SymmetricPoincareComplex

/-!
# The middle form

For a strict `4`-dimensional symmetric Poincaré complex `(C, φ)` in `Kar Free(ℚ[G])`, the
component `φ_2 : C_2^* → C_2` maps real `2`-cocycles to real `2`-cycles and coboundaries to
boundaries, and the middle form is `b_C([x], [y]) = ⟨[x], [φ_2 y]⟩` on `H^2(C; ℝ)`
(`HSP.middleForm`, `HSP.middleForm_mk`).

The component `φ_2` is `φ_{2,2} : (C_2)^* → C_2`. The cycle condition `∂φ = 0` in the component
`(1, 2)` reads `d φ_2 - φ_{1,3} d^* = 0`, so `φ_2` sends a cocycle to a cycle; in the component
`(2, 1)` it reads `d φ_{3,1} + φ_2 d^* = 0`, so `φ_2` sends a coboundary to a boundary.
-/

open CategoryTheory CategoryTheory.Idempotents

namespace HSP

open DualCat FreeCat

variable {G : Type} [AddGroup G] [Fintype G] [DecidableEq G]
  (x : SymPoincare (Karoubi (FreeCat G)) 4)

/-- The cycle condition `∂φ = 0` in the component `(p, q)`. -/
private theorem cycle_comp (p q : ℤ) (h : p + q = 4 - 1) (p' q' : ℤ) (hp' : p' + q = 4)
    (hq' : p + q' = 4) :
    x.φ ⟨(p', q), hp'⟩ ≫ x.C.d p' p + p.negOnePow • (dualHom (x.C.d q' q) ≫ x.φ ⟨(p, q'), hq'⟩) =
      0 := by
  have hc : StructureCx.dHom x.C 4 (4 - 1) x.φ = 0 := x.cycle
  have := congrFun hc ⟨(p, q), h⟩
  rwa [StructureCx.dHom_apply x.C 4 (4 - 1) x.φ p q h p' q' hp' hq'] at this

/-- `[y] ↦ [φ_2 y] : H^2(C; ℝ) → H_2(C; ℝ)`. -/
private noncomputable def phiMap : realHco x.C 2 →ₗ[ℝ] realH x.C 2 :=
  Submodule.mapQ _ _ ((realMap (x.φ ⟨(2, 2), by norm_num⟩).f).restrict fun y hy => by
      have h := cycle_comp x (2 - 1) 2 (by norm_num) 2 (2 + 1) (by norm_num) (by norm_num)
      rw [show ((2 : ℤ) - 1).negOnePow = -1 by rw [show (2 : ℤ) - 1 = 1 by norm_num]; rfl,
        Units.neg_smul, one_smul, ← sub_eq_add_neg, sub_eq_zero] at h
      have h' := congrArg (fun k => realMap k.f y) h
      simp only [Karoubi.comp_f, realMap_apply, mat_comp, Matrix.map_mul,
        ← Matrix.mulVec_mulVec] at h'
      refine ⟨⟨realMap (x.φ ⟨(2, 2), by norm_num⟩).f y, ?_⟩, LinearMap.mem_ker.2 ?_⟩
      · simp only [realMap_apply]
        rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, ← mat_comp, Karoubi.comp_p]
      · have hk := LinearMap.mem_ker.1 hy.2
        rw [realMap_apply] at hk
        simp only [realMap_apply] at hk ⊢
        rw [h', hk, Matrix.mulVec_zero])
    fun y hy => by
      obtain ⟨w, -, hw⟩ := hy
      have h := cycle_comp x 2 (2 - 1) (by norm_num) (2 + 1) 2 (by norm_num) (by norm_num)
      rw [Int.negOnePow_even 2 ⟨1, by norm_num⟩, one_smul, add_eq_zero_iff_neg_eq] at h
      have h' := congrArg (fun k => realMap k.f w) h
      have hneg : (-(x.φ ⟨(2 + 1, 2 - 1), by norm_num⟩ ≫ x.C.d (2 + 1) 2)).f =
          -(x.φ ⟨(2 + 1, 2 - 1), by norm_num⟩ ≫ x.C.d (2 + 1) 2).f := rfl
      simp only [hneg, Karoubi.comp_f, realMap_apply, mat_comp, mat_neg,
        Matrix.map_neg _ (map_neg (Rat.castHom ℝ)), Matrix.map_mul, Matrix.neg_mulVec,
        ← Matrix.mulVec_mulVec] at h'
      refine ⟨-realMap (x.φ ⟨(2 + 1, 2 - 1), by norm_num⟩).f w,
        ⟨-realMap (x.φ ⟨(2 + 1, 2 - 1), by norm_num⟩).f w, ?_⟩, ?_⟩
      · rw [map_neg]
        simp only [realMap_apply]
        rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, ← mat_comp, Karoubi.comp_p]
      · change _ = realMap (x.φ ⟨(2, 2), by norm_num⟩).f (y : G × Fin (x.C.X 2).X.n → ℝ)
        rw [show (y : G × Fin (x.C.X 2).X.n → ℝ) = _ from hw.symm, map_neg]
        simp only [realMap_apply]
        exact h'

/-- **The middle form** `b_C([x], [y]) = ⟨[x], [φ_2 y]⟩` on `H^2(C; ℝ)`. -/
noncomputable def middleForm : LinearMap.BilinForm ℝ (realHco x.C 2) :=
  (realEval x.C 2).compl₂ (phiMap x)

private theorem middleForm_mk (y z) :
    middleForm x (Submodule.Quotient.mk y) (Submodule.Quotient.mk z) =
      y.1 ⬝ᵥ realMap (x.φ ⟨(2, 2), by norm_num⟩).f z.1 := rfl

end HSP
