import HilbertSmithPaper.LTheory.Bounded.Categories.BoundedFunctor

/-!
# Bounded extensions of strict functors are strict

If `(F, ξ)` is strict, so is `C_ℤ(F, ξ)`: its duality isomorphism is the diagonal matrix of
identities.
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace HSP

open DualCat

universe v₁ v₂ u₁ u₂

namespace Bounded

variable {A : Type u₁} [Category.{v₁} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A]
  {A' : Type u₂} [Category.{v₂} A'] [Preadditive A'] [Linear ℚ A'] [HasFiniteBiproducts A']
  [DualCat A']

omit [HasFiniteBiproducts A] [DualCat A] in
private lemma eqToHom_eq_diag {M N : Bounded A} (h : M = N) :
    eqToHom h = diag fun n => eqToHom (congrArg (fun K : Bounded A => K.X n) h) := by
  subst h
  rfl

/-- **Bounded extensions of strict functors are strict.** If `(F, ξ)` is strict, so is its
bounded extension. -/
lemma map_isStrict {F : DualFunctor A A'} (hF : F.IsStrict) : (map F).IsStrict := by
  intro M
  have hobj : (map F).toFunctor.obj (dual M) = dual ((map F).toFunctor.obj M) :=
    Bounded.ext (funext fun n => (hF (M.X n)).choose)
  refine ⟨hobj, ?_⟩
  rw [map_ξ_hom, eqToHom_eq_diag]
  congr 1
  funext n
  exact (hF (M.X n)).choose_spec

end Bounded

end HSP

end
