import HilbertSmithPaper.LTheory.Base.Categories.DualityFunctor
import HilbertSmithPaper.LTheory.Bounded.Categories.BoundedDuality
import HilbertSmithPaper.LTheory.Bounded.Categories.IteratedBoundedCategory
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

/-- The entrywise functor `C_ℤ F`. -/
def mapFunctor (F : A ⥤ A') [F.Additive] : Bounded A ⥤ Bounded A' where
  obj M := ⟨fun n => F.obj (M.X n)⟩
  map {M N} f := ⟨fun m n => F.map (f.1 m n), by
    obtain ⟨r, hr⟩ := f.2
    exact ⟨r, fun m n h => by
      show F.map (f.1 m n) = 0
      rw [hr m n h, F.map_zero]⟩⟩
  map_id M := hom_ext fun m n => by
    change F.map (diagF (fun n => 𝟙 (M.X n)) m n) =
      diagF (M := ⟨fun n => F.obj (M.X n)⟩) (N := ⟨fun n => F.obj (M.X n)⟩)
        (fun n => 𝟙 (F.obj (M.X n))) m n
    by_cases h : m = n
    · subst h; rw [diagF_self, diagF_self, F.map_id]
    · rw [diagF_ne _ h, diagF_ne _ h, F.map_zero]
  map_comp {M N P} f g := hom_ext fun l n => by
    obtain ⟨r, hr⟩ := f.2
    have hs : ∀ m ∉ Finset.Icc (n - r) (n + r), f.1 m n = 0 := fun m hm =>
      hr m n (by rw [Finset.mem_Icc] at hm; rw [lt_abs]; omega)
    change F.map (compF f.1 g.1 l n) = compF (M := ⟨fun n => F.obj (M.X n)⟩)
      (N := ⟨fun n => F.obj (N.X n)⟩) (P := ⟨fun n => F.obj (P.X n)⟩)
      (fun m n => F.map (f.1 m n)) (fun m n => F.map (g.1 m n)) l n
    rw [compF_eq_sum _ _ l n _ (fun m hm => by rw [hs m hm, zero_comp]),
      compF_eq_sum _ _ l n (Finset.Icc (n - r) (n + r))
        (fun m hm => by simp only; rw [hs m hm, F.map_zero, zero_comp]),
      F.map_sum]
    exact Finset.sum_congr rfl fun m _ => F.map_comp _ _

omit [HasFiniteBiproducts A] [DualCat A] [HasFiniteBiproducts A'] [DualCat A'] in
lemma mapFunctor_map_apply (F : A ⥤ A') [F.Additive] {M N : Bounded A} (f : M ⟶ N) (m n : ℤ) :
    ((mapFunctor F).map f).1 m n = F.map (f.1 m n) := rfl

instance (F : A ⥤ A') [F.Additive] : (mapFunctor F).Additive where
  map_add := hom_ext fun _ _ => F.map_add

instance (F : A ⥤ A') [F.Additive] [F.Linear ℚ] : (mapFunctor F).Linear ℚ where
  map_smul _ _ := hom_ext fun _ _ => F.map_smul _ _

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
