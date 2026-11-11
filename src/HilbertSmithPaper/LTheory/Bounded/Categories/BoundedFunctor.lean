import HilbertSmithPaper.LTheory.Base.Categories.DualityFunctor
import HilbertSmithPaper.LTheory.Bounded.Categories.BoundedDuality
import HilbertSmithPaper.LTheory.Bounded.Categories.IteratedBoundedCategory
import HilbertSmithPaper.LTheory.Bounded.Categories.EntrywiseFunctor
import HilbertSmithPaper.LTheory.Bounded.Categories.BoundedDiag

/-!
# Bounded extension of a duality functor

For a duality functor `(F, ξ) : A → A'`, `C_ℤ(F, ξ) : C_ℤ(A) → C_ℤ(A')` applies `F` entrywise:
`(M_n) ↦ (F M_n)`, `(f_{mn}) ↦ (F f_{mn})`, with duality isomorphism the diagonal matrix
`(ξ_{M_n})_n` (`Bounded.map`). If `F` is strict, so is `C_ℤ(F, ξ)` (`Bounded.map_isStrict`).
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

omit [HasFiniteBiproducts A'] [DualCat A'] in
private lemma diag_coe' {M N : Bounded A'} (d : ∀ n, M.X n ⟶ N.X n) : (diag d).1 = diagF d := rfl

/-- The diagonal isomorphism with entries `e n : M_n ≅ N_n`. -/
private def diagIso {M N : Bounded A'} (e : ∀ n, M.X n ≅ N.X n) : M ≅ N where
  hom := diag fun n => (e n).hom
  inv := diag fun n => (e n).inv
  hom_inv_id := by rw [diag_comp_diag]; simp only [Iso.hom_inv_id]; rfl
  inv_hom_id := by rw [diag_comp_diag]; simp only [Iso.inv_hom_id]; rfl

/-- The *bounded extension* `C_ℤ(F, ξ)` of a duality functor: `F` entrywise, with duality
isomorphism the diagonal matrix `(ξ_{M_n})_n`. -/
def map (F : DualFunctor A A') : DualFunctor (Bounded A) (Bounded A') where
  toFunctor := mapFunctor F.toFunctor
  ξ M := diagIso (M := ⟨fun n => F.toFunctor.obj (dual (M.X n))⟩)
    (N := ⟨fun n => dual (F.toFunctor.obj (M.X n))⟩) fun n => F.ξ (M.X n)
  ξ_natural {M N} f := hom_ext fun a b =>
    (compF_diagF (M := ⟨fun n => F.toFunctor.obj (dual (N.X n))⟩)
      (N := ⟨fun n => F.toFunctor.obj (dual (M.X n))⟩)
      (P := ⟨fun n => dual (F.toFunctor.obj (M.X n))⟩)
      (fun m n => F.toFunctor.map (dualHom (f.1 n m))) (fun n => (F.ξ (M.X n)).hom) a b).trans
    ((F.ξ_natural (f.1 b a)).trans
      (diagF_compF (M := ⟨fun n => F.toFunctor.obj (dual (N.X n))⟩)
        (N := ⟨fun n => dual (F.toFunctor.obj (N.X n))⟩)
        (P := ⟨fun n => dual (F.toFunctor.obj (M.X n))⟩)
        (fun n => (F.ξ (N.X n)).hom) (fun m n => dualHom (F.toFunctor.map (f.1 n m))) a b).symm)
  ξ_dual M := hom_ext fun a b => by
    rw [eqToHom_comp_apply, dualHom_apply]
    simp only [diagIso, diag_coe']
    by_cases h : a = b
    · subst h
      rw [diagF_self, diagF_self]
      exact F.ξ_dual (M.X a)
    · rw [diagF_ne _ (Ne.symm h), diagF_ne _ h]
      exact dualHom_zero.trans comp_zero.symm

lemma map_ξ_hom (F : DualFunctor A A') (M : Bounded A) :
    ((map F).ξ M).hom = diag (M := ⟨fun n => F.toFunctor.obj (dual (M.X n))⟩)
      (N := ⟨fun n => dual (F.toFunctor.obj (M.X n))⟩) fun n => (F.ξ (M.X n)).hom := rfl

/-- If `(F, ξ)` is strict, so is its bounded extension. -/
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
