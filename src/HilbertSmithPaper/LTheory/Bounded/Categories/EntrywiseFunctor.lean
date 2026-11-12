import HilbertSmithPaper.LTheory.Bounded.Categories.BoundedDuality
import HilbertSmithPaper.LTheory.Bounded.Categories.IteratedBoundedCategory

/-!
# The entrywise functor

An additive functor `F : A ⥤ A'` gives `C_ℤ F : C_ℤ(A) ⥤ C_ℤ(A')`, `(M_n) ↦ (F M_n)`,
`(f_{mn}) ↦ (F f_{mn})`; it keeps the propagation of a matrix, and it is additive (and ℚ-linear
when `F` is).
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

omit [DualCat A] [DualCat A'] in
/-- **The entrywise functor.** `C_ℤ F`. -/
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

omit [DualCat A] [DualCat A'] in
instance (F : A ⥤ A') [F.Additive] : (mapFunctor F).Additive where
  map_add := hom_ext fun _ _ => F.map_add

omit [DualCat A] [DualCat A'] in
instance (F : A ⥤ A') [F.Additive] [F.Linear ℚ] : (mapFunctor F).Linear ℚ where
  map_smul _ _ := hom_ext fun _ _ => F.map_smul _ _

end Bounded

end HSP

end
