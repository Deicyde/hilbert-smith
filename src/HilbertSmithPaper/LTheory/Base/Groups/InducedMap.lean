import HilbertSmithPaper.LTheory.Base.Groups.LGroupAdd
import HilbertSmithPaper.LTheory.Base.Groups.InducedMapLaws
import HilbertSmithPaper.LTheory.Base.Categories.KaroubiFunctor
import HilbertSmithPaper.LTheory.Base.Groups.ProjectiveLGroup

/-!
# Induced homomorphism

A duality functor `(F, ξ) : B → B'` induces a homomorphism `F_* : L_k(B) → L_k(B')`,
`[C, φ] ↦ [F C, F_% φ]`. It is well defined and additive by `SymPoincare.map_cobordant`. On
projective L-groups a duality functor `F : A → A'` acts by `F_* = (Kar F)_*` (`Lp.map`).
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents

namespace HSP

universe v₁ v₂ u₁ u₂

variable {B : Type u₁} [Category.{v₁} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B]
  {B' : Type u₂} [Category.{v₂} B'] [Preadditive B'] [Linear ℚ B'] [HasFiniteBiproducts B']
  [DualCat B']

/-- The homomorphism `F_* : L_k(B) → L_k(B')`, `[C, φ] ↦ [F C, F_% φ]`, induced by a duality
functor. -/
noncomputable def LGroup.map (F : DualFunctor B B') (k : ℤ) : LGroup B k →+ LGroup B' k :=
  AddMonoidHom.mk' (Quotient.map (SymPoincare.map F) (fun x y h =>
    (SymPoincare.map_cobordant F).1 x y h)) (by
    intro a b
    induction a using Quotient.ind
    induction b using Quotient.ind
    exact Quotient.sound ((SymPoincare.map_cobordant F).2 _ _))

lemma LGroup.map_mk (F : DualFunctor B B') {k : ℤ} (x : SymPoincare B k) :
    LGroup.map F k (LGroup.mk x) = LGroup.mk (x.map F) :=
  rfl

/-- On projective L-groups a duality functor `F : A → A'` acts by `(Kar F)_*`. -/
noncomputable abbrev Lp.map (F : DualFunctor B B') (k : ℤ) : Lp B k →+ Lp B' k :=
  LGroup.map F.kar k

end HSP
