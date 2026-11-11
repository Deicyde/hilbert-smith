import HilbertSmithPaper.LTheory.Bounded.Categories.IteratedBoundedFiltration
import HilbertSmithPaper.LTheory.Bounded.Categories.BoundedFunctor
import HilbertSmithPaper.LTheory.Base.Categories.DualSubcategory
import HilbertSmithPaper.LTheory.Bounded.Categories.IteratedBoundedSub
import HilbertSmithPaper.LTheory.Bounded.Categories.BoundedKaroubiFiltration

/-!
# Iterated bounded categories of a subcategory

For a full additive subcategory `𝒰 ⊂ 𝒜` closed under duality and `j ≥ 0`, the full subcategory
`C_{ℤ^j}𝒰 ⊂ C_{ℤ^j}𝒜` (objects with all entries in `𝒰`, iterated) is identified with the iterated
bounded category `C_{ℤ^j}(𝒰)` of `𝒰` itself by a duality functor: the identity for `j = 0`,
and for `j + 1` the functor reading an object of `C_ℤ(C_{ℤ^j}𝒰)` as a family of objects of the
full subcategory `C_{ℤ^j}𝒰`, followed by the bounded extension of the identification at level `j`.
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace HSP

open DualCat

universe v u

namespace Bounded

section Restrict

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℚ C] [HasFiniteBiproducts C]
  [DualCat C] (V : ObjectProperty C) [IsDualAdditive V]

/-- An object of `C_ℤ(V) ⊂ C_ℤ(C)` as a family of objects of `V`. -/
private def restrictObj (M : (sub V).FullSubcategory) : Bounded V.FullSubcategory :=
  ⟨fun n => ⟨M.obj.X n, M.property n⟩⟩

omit [Linear ℚ C] [HasFiniteBiproducts C] [DualCat C] [IsDualAdditive V] in
private lemma hom_diagF {M N : Bounded V.FullSubcategory} (d : ∀ n, M.X n ⟶ N.X n) (m n : ℤ) :
    (diagF d m n).hom = diagF (M := ⟨fun n => (M.X n).obj⟩) (N := ⟨fun n => (N.X n).obj⟩)
      (fun n => (d n).hom) m n := by
  by_cases h : m = n
  · subst h
    rw [diagF_self, diagF_self]
  · rw [diagF_ne _ h, diagF_ne _ h]
    rfl

/-- Reading `C_ℤ(V) ⊂ C_ℤ(C)` as `C_ℤ` of the full subcategory `V`. -/
private def restrictFunctor : (sub V).FullSubcategory ⥤ Bounded V.FullSubcategory where
  obj := restrictObj V
  map {M N} f := ⟨fun m n => ObjectProperty.homMk (f.hom.1 m n), by
    obtain ⟨r, hr⟩ := f.hom.2
    exact ⟨r, fun m n h => ObjectProperty.hom_ext _ (hr m n h)⟩⟩
  map_id M := hom_ext fun m n => ObjectProperty.hom_ext _ (by
    change diagF (M := M.obj) (N := M.obj) (fun n => 𝟙 (M.obj.X n)) m n =
      (diagF (M := restrictObj V M) (N := restrictObj V M) (fun n => 𝟙 _) m n).hom
    rw [hom_diagF]
    rfl)
  map_comp {M N P} f g := hom_ext fun l n => ObjectProperty.hom_ext _ (by
    obtain ⟨r, hr⟩ := f.hom.2
    change compF f.hom.1 g.hom.1 l n = (compF (M := restrictObj V M) (N := restrictObj V N)
      (P := restrictObj V P) (fun m n => ObjectProperty.homMk (f.hom.1 m n))
      (fun m n => ObjectProperty.homMk (g.hom.1 m n)) l n).hom
    rw [compF_eq_sum _ _ l n (Finset.Icc (n - r) (n + r)) (fun m hm => by
        rw [hr m n (by rw [Finset.mem_Icc] at hm; rw [lt_abs]; omega), zero_comp]),
      compF_eq_sum _ _ l n (Finset.Icc (n - r) (n + r)) (fun m hm => ObjectProperty.hom_ext _ (by
        change f.hom.1 m n ≫ g.hom.1 l m = 0
        rw [hr m n (by rw [Finset.mem_Icc] at hm; rw [lt_abs]; omega), zero_comp]))]
    exact (Functor.map_sum V.ι (fun m => (ObjectProperty.homMk (f.hom.1 m n) :
      (restrictObj V M).X n ⟶ (restrictObj V N).X m) ≫ (ObjectProperty.homMk (g.hom.1 l m) :
      (restrictObj V N).X m ⟶ (restrictObj V P).X l)) (Finset.Icc (n - r) (n + r))).symm)

private instance : (restrictFunctor V).Additive where
  map_add := hom_ext fun _ _ => ObjectProperty.hom_ext _ rfl

private instance : (restrictFunctor V).Linear ℚ where
  map_smul _ _ := hom_ext fun _ _ => ObjectProperty.hom_ext _ rfl

/-- `C_ℤ(V) ⊂ C_ℤ(C)` as `C_ℤ` of the full subcategory `V`, a strict duality functor. -/
private def restrict : DualFunctor (sub V).FullSubcategory (Bounded V.FullSubcategory) where
  toFunctor := restrictFunctor V
  ξ M := Iso.refl _
  ξ_natural f := by
    rw [Iso.refl_hom, Iso.refl_hom]
    erw [Category.comp_id, Category.id_comp]
    exact hom_ext fun _ _ => ObjectProperty.hom_ext _ rfl
  ξ_dual M := by
    rw [Iso.refl_hom, Iso.refl_hom]
    erw [dualHom_id, Category.comp_id]
    rfl

end Restrict

variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A] (U : ObjectProperty A) [IsDualAdditive U]

/-- The identification `C_{ℤ^j}𝒰 → C_{ℤ^j}(𝒰)` of the full subcategory `C_{ℤ^j}𝒰 ⊂ C_{ℤ^j}𝒜`
with the iterated bounded category of `𝒰`: the identity for `j = 0`, and for `j + 1` the reading
of `C_ℤ(C_{ℤ^j}𝒰) ⊂ C_ℤ(C_{ℤ^j}𝒜)` as `C_ℤ` of the full subcategory `C_{ℤ^j}𝒰`, followed by
the bounded extension of the identification at level `j`. -/
def subPowIdent : ∀ j : ℕ,
    DualFunctor (subPow U j).FullSubcategory (BoundedPow U.FullSubcategory j)
  | 0 => DualFunctor.id _
  | j + 1 => (restrict (subPow U j)).comp (Bounded.map (subPowIdent j))

end Bounded

end HSP
