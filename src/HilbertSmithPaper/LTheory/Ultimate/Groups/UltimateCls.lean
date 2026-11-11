import HilbertSmithPaper.LTheory.Ultimate.Groups.UltimateStageMap

/-!
# The class map

`cls : L^p_k(A) → 𝕃_k(A)` is `ι_0` under `L^p_k(A) = L^{⟨0⟩}_k(A)`.

Lean: `L^{⟨0⟩}_k(A) = L^p_{k+0}(C_{ℤ^0} A)`, so `cls` precomposes `ι_0` with the transport
`LGroup.castIndex` of L-groups along the equality of degrees `k = k + 0`.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents

namespace HSP

universe v u

/-- Transport of `L`-groups along an equality of degrees. -/
noncomputable def LGroup.castIndex {B : Type u} [Category.{v} B] [Preadditive B] [Linear ℚ B]
    [HasFiniteBiproducts B] [DualCat B] {m m' : ℤ} (h : m = m') : LGroup B m ≃+ LGroup B m' := by
  subst h
  exact AddEquiv.refl _

variable (A : Type u) [Category.{v} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A]

/-- `cls = ι_0 : L^p_k(A) → 𝕃_k(A)`. -/
noncomputable def cls (k : ℤ) : Lp A k →+ ultL A k :=
  (ultL.of A k 0).comp
    (LGroup.castIndex (B := Karoubi A) (show k = k + ((0 : ℕ) : ℤ) by simp)).toAddMonoidHom

end HSP
