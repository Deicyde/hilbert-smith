import HilbertSmithPaper.LTheory.Base.Categories.FiltrationQuotient
import HilbertSmithPaper.LTheory.Bounded.Categories.BoundedKaroubiFiltration
import HilbertSmithPaper.LTheory.Bounded.Categories.BoundedQuotientFunctor
import HilbertSmithPaper.LTheory.Bounded.Categories.BoundedFunctor
import HilbertSmithPaper.LTheory.Bounded.Categories.BoundedSub
import HilbertSmithPaper.LTheory.Bounded.Categories.BoundedSubAdditive

/-!
# Bounded quotients

For an involution-invariant Karoubi filtration of `A` by `U`, the entrywise quotient functor
`Bounded.quotientFunctor U : C_ℤ(A)/C_ℤ(U) → C_ℤ(A/U)` is an isomorphism of duality
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

variable {U}

/-- For finitely many maps in `I_𝒰` into `X`, some chosen decomposition of `X` fixes them all. -/
private lemma exists_fix_finset (F : KaroubiFiltration U) {X : A} {ι : Type*} (s : Finset ι)
    (Y : ι → A) (g : ∀ i, Y i ⟶ X) (hg : ∀ i ∈ s, FiltQuot.ideal U (g i)) :
    ∃ p ∈ F.D X, ∀ i ∈ s, g i ≫ p = g i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨p, hp⟩ := F.nonempty X
    exact ⟨p, hp, by simp⟩
  | insert a s ha ih =>
    obtain ⟨p, hp, hps⟩ := ih fun i hi => hg i (Finset.mem_insert_of_mem hi)
    obtain ⟨V, hV, x, y, hxy⟩ := hg a (Finset.mem_insert_self a s)
    obtain ⟨q, hq, hqa⟩ := F.factor_left y hV
    obtain ⟨p'', hp'', ⟨h1, -⟩, ⟨h2, -⟩⟩ := F.directed hp hq
    refine ⟨p'', hp'', fun i hi => ?_⟩
    rcases Finset.mem_insert.1 hi with rfl | hi
    · rw [hxy, Category.assoc, ← hqa, Category.assoc, h2]
    · rw [← hps i hi, Category.assoc, h1]

/-- A bounded map all of whose entries lie in `I_𝒰` factors through `C_ℤ(U)`. -/
private lemma ideal_sub_of_forall (F : KaroubiFiltration U) {M N : Bounded A} (f : M ⟶ N)
    (hf : ∀ l n, FiltQuot.ideal U (f.1 l n)) : FiltQuot.ideal (sub U) f := by
  obtain ⟨r, hr⟩ := f.2
  choose p hp hpf using fun l : ℤ => exists_fix_finset F (Finset.Icc (l - r) (l + r)) M.X
    (fun n => f.1 l n) (fun n _ => hf l n)
  choose E hE i ρ hiρ hρi using fun l => F.split (hp l)
  refine ⟨⟨E⟩, hE, f ≫ diag (M := N) (N := ⟨E⟩) ρ, diag (M := ⟨E⟩) (N := N) i, ?_⟩
  rw [Category.assoc, diag_comp_diag]
  refine hom_ext fun l n => ?_
  change f.1 l n = compF f.1 (diagF fun n => ρ n ≫ i n) l n
  rw [compF_diagF, hρi]
  by_cases hn : n ∈ Finset.Icc (l - r) (l + r)
  · exact (hpf l n hn).symm
  · rw [hr l n (by rw [Finset.mem_Icc] at hn; rw [lt_abs]; omega), zero_comp]

/-- The entrywise quotient functor is faithful modulo `C_ℤ(U)`. -/
private lemma functor_map_eq_of_map_eq (F : KaroubiFiltration U) {M N : Bounded A}
    {h h' : M ⟶ N}
    (e : (mapFunctor (FiltQuot.functor U)).map h = (mapFunctor (FiltQuot.functor U)).map h') :
    (FiltQuot.functor (sub U)).map h = (FiltQuot.functor (sub U)).map h' := by
  rw [FiltQuot.functor_map_eq_iff]
  refine ideal_sub_of_forall F _ fun l n => ?_
  have := congrArg (fun k => k.1 l n) e
  exact (FiltQuot.functor_map_eq_iff U _ _).1 this

/-- The entrywise lift of a morphism of `C_ℤ(A/U)`, lifting zero entries to zero. -/
private def liftE {X Y : Bounded (FiltQuot U)} (g : X ⟶ Y) :
    (⟨fun n => (X.X n).as⟩ : Bounded A) ⟶ ⟨fun n => (Y.X n).as⟩ := by
  refine ⟨fun m n => haveI := Classical.propDecidable (g.1 m n = 0); if g.1 m n = 0 then 0 else
    (FiltQuot.functor_map_surjective U (g.1 m n)).choose, ?_⟩
  obtain ⟨r, hr⟩ := g.2
  exact ⟨r, fun m n h => by simp [hr m n h]⟩

private lemma map_liftE {X Y : Bounded (FiltQuot U)} (g : X ⟶ Y) :
    (mapFunctor (FiltQuot.functor U)).map (liftE g) = g := hom_ext fun m n => by
  change (FiltQuot.functor U).map
    (@ite _ (g.1 m n = 0) (Classical.propDecidable _) 0 _) = g.1 m n
  split_ifs with h
  · rw [h]; exact (FiltQuot.functor U).map_zero _ _
  · exact (FiltQuot.functor_map_surjective U (g.1 m n)).choose_spec

/-- The inverse functor `C_ℤ(A/U) → C_ℤ(A)/C_ℤ(U)`: lift entrywise. -/
private def invF (F : KaroubiFiltration U) : Bounded (FiltQuot U) ⥤ FiltQuot (sub U) where
  obj X := (FiltQuot.functor (sub U)).obj ⟨fun n => (X.X n).as⟩
  map g := (FiltQuot.functor (sub U)).map (liftE g)
  map_id X := by
    rw [← (FiltQuot.functor (sub U)).map_id]
    refine functor_map_eq_of_map_eq F ?_
    rw [map_liftE]
    exact ((mapFunctor (FiltQuot.functor U)).map_id (⟨fun n => (X.X n).as⟩ : Bounded A)).symm
  map_comp g h := by
    rw [← (FiltQuot.functor (sub U)).map_comp]
    refine functor_map_eq_of_map_eq F ?_
    rw [map_liftE, Functor.map_comp, map_liftE, map_liftE]
    rfl

private lemma invF_map (F : KaroubiFiltration U) {X Y : Bounded (FiltQuot U)} (g : X ⟶ Y) :
    (invF F).map g = (FiltQuot.functor (sub U)).map (liftE g) := rfl

private instance (F : KaroubiFiltration U) : (invF F).Additive where
  map_add {X Y g h} := by
    rw [invF_map, invF_map, invF_map]
    refine (functor_map_eq_of_map_eq F (h' := liftE g + liftE h) ?_).trans
      ((FiltQuot.functor (sub U)).map_add)
    rw [map_liftE, Functor.map_add, map_liftE, map_liftE]
    rfl

private instance (F : KaroubiFiltration U) : (invF F).Linear ℚ where
  map_smul {X Y} g c := by
    rw [invF_map, invF_map]
    refine (functor_map_eq_of_map_eq F (h' := c • liftE g) ?_).trans
      ((FiltQuot.functor (sub U)).map_smul _ _)
    rw [map_liftE, Functor.map_smul, map_liftE]
    rfl

/-- The inverse as a duality functor, with identity duality isomorphism. -/
private def invDual (F : KaroubiFiltration U) :
    DualFunctor (Bounded (FiltQuot U)) (FiltQuot (sub U)) where
  toFunctor := invF F
  ξ X := Iso.refl _
  ξ_natural {X Y} g := by
    refine (Category.comp_id _).trans (Eq.trans ?_ (Category.id_comp _).symm)
    rw [invF_map]
    refine (functor_map_eq_of_map_eq F ?_).trans rfl
    rw [map_liftE]
    exact (congrArg dualHom (map_liftE g)).symm.trans (hom_ext fun a b => rfl)
  ξ_dual X := by
    erw [dualHom_id, Category.comp_id]
    exact (eqToHom_refl _ _).symm

/-- **Bounded quotients.** For an involution-invariant Karoubi filtration of `A` by `U`, the
entrywise quotient functor `C_ℤ(A)/C_ℤ(U) → C_ℤ(A/U)` is an isomorphism of duality categories:
it has a strict duality functor inverse, and both composites are the identity functors. -/
theorem quotientEquiv (U : ObjectProperty A) [IsDualAdditive U] (F : KaroubiFiltration U) :
    ∃ G : DualFunctor (Bounded (FiltQuot U)) (FiltQuot (sub U)), G.IsStrict ∧
      (quotientFunctor U).toFunctor ⋙ G.toFunctor = 𝟭 _ ∧
      G.toFunctor ⋙ (quotientFunctor U).toFunctor = 𝟭 _ := by
  refine ⟨invDual F, fun _ => ⟨rfl, rfl⟩, ?_, ?_⟩
  · refine CategoryTheory.Functor.hext (fun _ => rfl) fun M N f => heq_of_eq ?_
    obtain ⟨f, rfl⟩ := FiltQuot.functor_map_surjective (sub U) f
    exact functor_map_eq_of_map_eq F (map_liftE _)
  · refine CategoryTheory.Functor.hext (fun _ => rfl) fun X Y g => heq_of_eq ?_
    exact map_liftE g

end Bounded

end HSP

end
