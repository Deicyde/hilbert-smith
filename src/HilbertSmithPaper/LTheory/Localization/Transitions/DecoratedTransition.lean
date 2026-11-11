import Mathlib
import HilbertSmithPaper.LTheory.Localization.Decorations.DecoratedLGroup
import HilbertSmithPaper.LTheory.Localization.Transitions.DecoratedTransitionCobordant
import HilbertSmithPaper.LTheory.Localization.Transitions.DecoratedTransitionSum

/-!
# Decorated transition

For an involution-invariant Karoubi filtration `𝒰 ⊂ 𝒜`, `j ≥ 0` and `m' = m + 1`, the decorated
transition `t^{im} : L^p_m(C_{ℤ^j}(𝒜/𝒰)) → L^{im}_{m'}(C_{ℤ^{j+1}}𝒜/C_{ℤ^{j+1}}𝒰)`,
`[C, φ] ↦ [e_{j+1}^{-1}(C ⊗ Λ), (e_{j+1}^{-1})_%(φ ⊗ λ)]`, a homomorphism.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents

namespace HSP

universe v u

variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A] {U : ObjectProperty A} [IsDualAdditive U]

/-- **Decorated transition.** `t^{im}[C, φ] = [e_{j+1}^{-1}(C ⊗ Λ), (e_{j+1}^{-1})_%(φ ⊗ λ)]`. -/
noncomputable def decTransition (F : KaroubiFiltration U) (j : ℕ) {m m' : ℤ} (hm : m + 1 = m') :
    Lp (BoundedPow (FiltQuot U) j) m →+ LIm (Bounded.subPow U (j + 1)) m' :=
  AddMonoidHom.mk' (Quotient.lift (fun x => LGroup.mk (decTransitionCx F j hm x))
    fun _ _ h => Quotient.sound (decTransitionCx_cobordant F j hm h)) fun a b => by
    induction a using Quotient.ind
    induction b using Quotient.ind
    exact decTransitionCx_sum F j hm _ _

/-- The value of `t^{im}` on a class. -/
lemma decTransition_mk (F : KaroubiFiltration U) (j : ℕ) {m m' : ℤ} (hm : m + 1 = m')
    (x : SymPoincare (Karoubi (BoundedPow (FiltQuot U) j)) m) :
    decTransition F j hm (LGroup.mk x) = LGroup.mk (decTransitionCx F j hm x) :=
  rfl

end HSP
