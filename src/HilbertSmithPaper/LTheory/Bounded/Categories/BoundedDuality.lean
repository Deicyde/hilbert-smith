import HilbertSmithPaper.LTheory.Bounded.Categories.BoundedCategory

/-!
# The induced duality on `C_ℤ(A)`

For a duality category `A`, `C_ℤ(A)` is a duality category with `(M^*)_n = (M_n)^*` and
`(f^*)_{nm} = (f_{mn})^*`; `f^*` has the same propagation as `f`, and `M^{**} = M`,
`f^{**} = f` hold on the nose (the latter with the transports along `M^{**} = M`, as in
`HSP.DualCat`).
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace HSP

open DualCat

universe v u

namespace Bounded

variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℚ A]

omit [Linear ℚ A] in
private lemma abs_sub_comm' (a b : ℤ) : |a - b| = |b - a| := abs_sub_comm a b

lemma eqToHom_comp_apply {M M' N : Bounded A} (h : M' = M) (f : M ⟶ N) (m n : ℤ) :
    (eqToHom h ≫ f).1 m n = eqToHom (congrArg (fun K : Bounded A => K.X n) h) ≫ f.1 m n := by
  subst h
  simp

lemma comp_eqToHom_apply {M N N' : Bounded A} (f : M ⟶ N) (h : N = N') (m n : ℤ) :
    (f ≫ eqToHom h).1 m n = f.1 m n ≫ eqToHom (congrArg (fun K : Bounded A => K.X m) h) := by
  subst h
  simp

variable [HasFiniteBiproducts A] [DualCat A]

private lemma dualHom_sum' {X Y : A} {ι : Type*} (s : Finset ι) (f : ι → (X ⟶ Y)) :
    dualHom (∑ i ∈ s, f i) = ∑ i ∈ s, dualHom (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, dualHom_add, ih]

/-- The dual of a bounded morphism: `(f^*)_{ab} = (f_{ba})^*`, of the same propagation. -/
def dualHomB {M N : Bounded A} (f : M ⟶ N) :
    (⟨fun n => dual (N.X n)⟩ : Bounded A) ⟶ ⟨fun n => dual (M.X n)⟩ :=
  ⟨fun a b => dualHom (f.1 b a), by
    obtain ⟨r, hr⟩ := f.2
    exact ⟨r, fun a b h => by
      show dualHom (f.1 b a) = 0
      rw [hr b a (by rwa [abs_sub_comm']), dualHom_zero]⟩⟩

private lemma dualHomB_id (M : Bounded A) :
    dualHomB (𝟙 M) = 𝟙 (⟨fun n => dual (M.X n)⟩ : Bounded A) := hom_ext fun a b => by
  change dualHom (diagF (fun n => 𝟙 (M.X n)) b a) =
    diagF (M := ⟨fun n => dual (M.X n)⟩) (N := ⟨fun n => dual (M.X n)⟩)
      (fun n => 𝟙 (dual (M.X n))) a b
  by_cases h : a = b
  · subst h; rw [diagF_self, diagF_self, dualHom_id]
  · rw [diagF_ne _ (Ne.symm h), diagF_ne _ h, dualHom_zero]

/-- The induced duality on `C_ℤ(A)`: `(M^*)_n = (M_n)^*`, `(f^*)_{nm} = (f_{mn})^*`. -/
instance dualCat : DualCat (Bounded A) where
  dual M := ⟨fun n => dual (M.X n)⟩
  dualHom f := dualHomB f
  dualHom_id M := dualHomB_id M
  dualHom_comp {M N P} f g := hom_ext fun a b => by
    obtain ⟨s, hs⟩ : ∃ s : Finset ℤ, ∀ m ∉ s, f.1 m a = 0 := by
      obtain ⟨r, hr⟩ := f.2
      exact ⟨Finset.Icc (a - r) (a + r), fun m hm => hr m a (by
        rw [Finset.mem_Icc] at hm; rw [lt_abs]; omega)⟩
    change dualHom (compF f.1 g.1 b a) = compF (dualHomB g).1 (dualHomB f).1 a b
    rw [compF_eq_sum _ _ b a s (fun m hm => by rw [hs m hm, zero_comp]),
      compF_eq_sum _ _ a b s (fun m hm => by
        change dualHom (g.1 b m) ≫ dualHom (f.1 m a) = 0
        rw [hs m hm, dualHom_zero, comp_zero]), dualHom_sum']
    exact Finset.sum_congr rfl fun m _ => dualHom_comp _ _
  dualHom_add f g := hom_ext fun a b => dualHom_add (f.1 b a) (g.1 b a)
  dualHom_smul c f := hom_ext fun a b => dualHom_smul c (f.1 b a)
  dual_dual M := Bounded.ext (funext fun n => dual_dual (M.X n))
  dualHom_dualHom {M N} f := hom_ext fun m n => by
    rw [eqToHom_comp_apply, comp_eqToHom_apply]
    exact dualHom_dualHom (f.1 m n)
  dualHom_zero := hom_ext fun a b => dualHom_zero (M := _) (N := _)
  dualHom_neg f := hom_ext fun a b => dualHom_neg (f.1 b a)
  dualHom_sub f g := hom_ext fun a b => dualHom_sub (f.1 b a) (g.1 b a)
  dualHom_eqToHom := by
    rintro M _ rfl
    exact dualHomB_id M

lemma dual_X (M : Bounded A) (n : ℤ) : (dual M).X n = dual (M.X n) := rfl

lemma dualHom_apply {M N : Bounded A} (f : M ⟶ N) (a b : ℤ) :
    (dualHom f).1 a b = dualHom (f.1 b a) := rfl

end Bounded

end HSP

end
