import HilbertSmithPaper.LTheory.Ultimate.Groups.InducedMapLevel
import HilbertSmithPaper.LTheory.Ultimate.Groups.UltimateCls
import HilbertSmithPaper.LTheory.Base.Groups.LGroupCast

/-!
# The induced map commutes with cls

For a duality functor `F : A → A'`, `F_* ∘ cls = cls ∘ F_*`, where on the right
`F_* : L^p_k(A) → L^p_k(A')` is the induced homomorphism.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents

namespace HSP

universe v u

variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A]
  {A' : Type u} [Category.{v} A'] [Preadditive A'] [Linear ℚ A'] [HasFiniteBiproducts A']
  [DualCat A']

private lemma castIndex_map (F : DualFunctor A A') {m m' : ℤ} (h : m = m') (x : Lp A m) :
    LGroup.castIndex (B := Karoubi A') h (Lp.map F m x) =
      Lp.map F m' (LGroup.castIndex (B := Karoubi A) h x) := by
  subst h
  rfl

/-- `F_* ∘ cls = cls ∘ F_*`. -/
theorem ultL.map_cls (F : DualFunctor A A') (k : ℤ) :
    (ultL.map F k).comp (cls A k) = (cls A' k).comp (Lp.map F k) := by
  ext x
  have h := congrArg (fun f => f (LGroup.castIndex (B := Karoubi A)
    (show k = k + ((0 : ℕ) : ℤ) by simp) x)) (ultL.map_of F k 0)
  exact h.trans (congrArg (ultL.of A' k 0) (castIndex_map F _ x).symm)

end HSP
