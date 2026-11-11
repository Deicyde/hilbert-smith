import HilbertSmithPaper.LTheory.Base.Categories.FiltrationQuotient
import HilbertSmithPaper.LTheory.Bounded.Categories.BoundedKaroubiFiltration
import HilbertSmithPaper.LTheory.Bounded.Categories.BoundedFunctor

/-!
# Bounded quotients

For an involution-invariant Karoubi filtration of `A` by `U`, the entrywise quotient functor
`C_ℤ(A) → C_ℤ(A/U)` kills the maps factoring through `C_ℤ(U)`, so it descends to
`Bounded.quotientFunctor U : C_ℤ(A)/C_ℤ(U) → C_ℤ(A/U)`, a strict duality functor that is the
identity on objects. The theorem `Bounded.quotientEquiv` says it is an isomorphism of duality
categories: it has a strict duality functor inverse, with both composites the identity functors
(the paper's duality equivalence with identity unit and counit).
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace HSP

open DualCat

universe v u

namespace Bounded

variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A] (U : ObjectProperty A) [IsDualAdditive U]

/-- A finite sum of maps in the ideal `I_𝒰` is in the ideal. -/
private lemma ideal_sum {X Y : A} {ι : Type*} (s : Finset ι) (f : ι → (X ⟶ Y))
    (hf : ∀ i ∈ s, FiltQuot.ideal U (f i)) : FiltQuot.ideal U (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using FiltQuot.ideal_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact FiltQuot.ideal_add (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- Every entry of a map factoring through `C_ℤ(U)` lies in `I_𝒰`. -/
lemma ideal_apply_of_ideal_sub {M N : Bounded A} {f : M ⟶ N}
    (hf : FiltQuot.ideal (sub U) f) (l n : ℤ) : FiltQuot.ideal U (f.1 l n) := by
  obtain ⟨V, hV, a, b, rfl⟩ := hf
  obtain ⟨r, hr⟩ := a.2
  rw [comp_apply, compF_eq_sum _ _ l n (Finset.Icc (n - r) (n + r)) (fun m hm => by
    rw [hr m n (by rw [Finset.mem_Icc] at hm; rw [lt_abs]; omega), zero_comp])]
  exact ideal_sum U _ _ fun m _ => ⟨V.X m, hV m, a.1 m n, b.1 l m, rfl⟩

private lemma map_eq_zero_of_ideal {M N : Bounded A} {f : M ⟶ N}
    (hf : FiltQuot.ideal (sub U) f) : (mapFunctor (FiltQuot.functor U)).map f = 0 :=
  hom_ext fun l n => by
    have h := (FiltQuot.functor_map_eq_iff U (f.1 l n) 0).2
      (by simpa using ideal_apply_of_ideal_sub U hf l n)
    rw [Functor.map_zero] at h
    exact h

/-- The functor `C_ℤ(A)/C_ℤ(U) → C_ℤ(A/U)` induced by the entrywise quotient functor. -/
def quotientFunctorF : FiltQuot (sub U) ⥤ Bounded (FiltQuot U) :=
  CategoryTheory.Quotient.lift _ (mapFunctor (FiltQuot.functor U)) fun _ _ f₁ f₂ h => by
    rw [← sub_eq_zero, ← Functor.map_sub]
    exact map_eq_zero_of_ideal U h

lemma quotientFunctorF_map {M N : Bounded A} (f : M ⟶ N) :
    (quotientFunctorF U).map ((FiltQuot.functor (sub U)).map f) =
      (mapFunctor (FiltQuot.functor U)).map f := rfl

instance : (quotientFunctorF U).Additive where
  map_add {M N f g} := by
    obtain ⟨f, rfl⟩ := FiltQuot.functor_map_surjective (sub U) f
    obtain ⟨g, rfl⟩ := FiltQuot.functor_map_surjective (sub U) g
    exact hom_ext fun l n => (FiltQuot.functor U).map_add

instance : (quotientFunctorF U).Linear ℚ where
  map_smul {M N} f c := by
    obtain ⟨f, rfl⟩ := FiltQuot.functor_map_surjective (sub U) f
    exact hom_ext fun l n => (FiltQuot.functor U).map_smul _ _

/-- The entrywise quotient functor `C_ℤ(A)/C_ℤ(U) → C_ℤ(A/U)` as a duality functor; it is the
identity on objects and its duality isomorphism is the identity. -/
def quotientFunctor : DualFunctor (FiltQuot (sub U)) (Bounded (FiltQuot U)) where
  toFunctor := quotientFunctorF U
  ξ M := Iso.refl _
  ξ_natural {M N} f := by
    obtain ⟨f, rfl⟩ := FiltQuot.functor_map_surjective (sub U) f
    exact (Category.comp_id _).trans ((hom_ext fun a b => rfl).trans (Category.id_comp _).symm)
  ξ_dual M := by
    erw [dualHom_id, Category.comp_id]
    exact (eqToHom_refl _ _).symm

/-- The entrywise quotient functor is strict. -/
lemma quotientFunctor_isStrict : (quotientFunctor U).IsStrict := fun _ => ⟨rfl, rfl⟩

/-- **Bounded quotients.** For an involution-invariant Karoubi filtration of `A` by `U`, the
entrywise quotient functor `C_ℤ(A)/C_ℤ(U) → C_ℤ(A/U)` is an isomorphism of duality categories:
it has a strict duality functor inverse, and both composites are the identity functors. -/
theorem quotientEquiv (F : KaroubiFiltration U) :
    ∃ G : DualFunctor (Bounded (FiltQuot U)) (FiltQuot (sub U)), G.IsStrict ∧
      (quotientFunctor U).toFunctor ⋙ G.toFunctor = 𝟭 _ ∧
      G.toFunctor ⋙ (quotientFunctor U).toFunctor = 𝟭 _ := by
  sorry

end Bounded

end HSP

end
