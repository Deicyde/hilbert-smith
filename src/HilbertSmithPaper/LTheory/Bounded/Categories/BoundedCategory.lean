import HilbertSmithPaper.LTheory.Base.Categories.DualityCategory

/-!
# The bounded category `C_ℤ(A)`

For a ℚ-linear additive category `A`, an object of `C_ℤ(A)` is a family `M = (M_n)_{n ∈ ℤ}` of
objects of `A` (the structure `Bounded A` with field `X : ℤ → A`; a structure rather than the
function type `ℤ → A`, which already carries Mathlib's product-category instance). A morphism
`f : M ⟶ N` is a family `f m n : M_n ⟶ N_m` with some propagation `r : ℕ`: `f m n = 0` whenever
`|m - n| > r`. The morphisms form the ℚ-submodule `Bounded.homSub M N` of all families, so the hom
types inherit their `AddCommGroup` and `Module ℚ` structures.

Composition (in diagrammatic order) is `(f ≫ g) l n = ∑ᶠ m, f m n ≫ g l m`, the paper's
`(gf)_{ln} = ∑_m g_{lm} f_{mn}`; the sum is a `finsum` whose support lies in the band of `f`, so it
is a finite sum (`Bounded.comp_apply_eq_sum`). Identities and the structure maps of biproducts are
diagonal families (`Bounded.diag`). Biproducts are taken degreewise.
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace HSP

universe v u

/-- An object of the bounded category `C_ℤ(A)`: a family `(M_n)_{n ∈ ℤ}` of objects of `A`. -/
@[ext]
structure Bounded (A : Type u) where
  /-- The object `M_n` in degree `n`. -/
  X : ℤ → A

namespace Bounded

variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℚ A]

/-- The bounded families `f m n : M_n ⟶ N_m`: those vanishing outside some band
`|m - n| ≤ r`. They form a ℚ-submodule of all families. -/
def homSub (M N : Bounded A) : Submodule ℚ (∀ m n : ℤ, M.X n ⟶ N.X m) where
  carrier := {f | ∃ r : ℕ, ∀ m n, (r : ℤ) < |m - n| → f m n = 0}
  add_mem' := by
    rintro f g ⟨r, hr⟩ ⟨s, hs⟩
    refine ⟨max r s, fun m n h => ?_⟩
    have h1 : (r : ℤ) < |m - n| := lt_of_le_of_lt (by exact_mod_cast le_max_left r s) h
    have h2 : (s : ℤ) < |m - n| := lt_of_le_of_lt (by exact_mod_cast le_max_right r s) h
    simp [hr m n h1, hs m n h2]
  zero_mem' := ⟨0, fun _ _ _ => rfl⟩
  smul_mem' := by
    rintro c f ⟨r, hr⟩
    exact ⟨r, fun m n h => by simp [hr m n h]⟩

private lemma lt_abs_of_not_mem {m n : ℤ} {r : ℕ} (h : m ∉ Finset.Icc (n - r) (n + r)) :
    (r : ℤ) < |m - n| := by
  rw [Finset.mem_Icc] at h
  rw [lt_abs]
  omega

/-- The composite family `(f ≫ g) l n = ∑ᶠ m, f m n ≫ g l m`. -/
def compF {M N P : Bounded A} (f : ∀ m n : ℤ, M.X n ⟶ N.X m) (g : ∀ m n : ℤ, N.X n ⟶ P.X m) :
    ∀ l n : ℤ, M.X n ⟶ P.X l :=
  fun l n => ∑ᶠ m, f m n ≫ g l m

omit [Linear ℚ A] in
lemma compF_eq_sum {M N P : Bounded A} (f : ∀ m n : ℤ, M.X n ⟶ N.X m)
    (g : ∀ m n : ℤ, N.X n ⟶ P.X m) (l n : ℤ) (s : Finset ℤ)
    (hs : ∀ m ∉ s, f m n ≫ g l m = 0) : compF f g l n = ∑ m ∈ s, f m n ≫ g l m := by
  refine finsum_eq_sum_of_support_subset _ fun m hm => ?_
  by_contra h
  exact hm (hs m h)

omit [Linear ℚ A] in
lemma compF_eq_zero {M N P : Bounded A} {f : ∀ m n : ℤ, M.X n ⟶ N.X m}
    {g : ∀ m n : ℤ, N.X n ⟶ P.X m} {r s : ℕ} (hr : ∀ m n, (r : ℤ) < |m - n| → f m n = 0)
    (hs : ∀ m n, (s : ℤ) < |m - n| → g m n = 0) {l n : ℤ} (h : ((r + s : ℕ) : ℤ) < |l - n|) :
    compF f g l n = 0 := by
  rw [compF_eq_sum f g l n (Finset.Icc (n - r) (n + r))
    (fun m hm => by rw [hr m n (lt_abs_of_not_mem hm), zero_comp])]
  refine Finset.sum_eq_zero fun m hm => ?_
  rw [Finset.mem_Icc] at hm
  have : (s : ℤ) < |l - m| := by
    rw [lt_abs] at h ⊢
    push_cast at h
    omega
  rw [hs l m this, comp_zero]

lemma compF_mem {M N P : Bounded A} {f : ∀ m n : ℤ, M.X n ⟶ N.X m}
    {g : ∀ m n : ℤ, N.X n ⟶ P.X m} (hf : f ∈ homSub M N) (hg : g ∈ homSub N P) :
    compF f g ∈ homSub M P := by
  obtain ⟨r, hr⟩ := hf
  obtain ⟨s, hs⟩ := hg
  exact ⟨r + s, fun l n h => compF_eq_zero hr hs h⟩

/-- The diagonal family with entries `d n : M_n ⟶ N_n` (propagation `0`). -/
def diagF {M N : Bounded A} (d : ∀ n, M.X n ⟶ N.X n) : ∀ m n : ℤ, M.X n ⟶ N.X m :=
  fun m n => if h : m = n then d n ≫ eqToHom (congrArg N.X h.symm) else 0

omit [Linear ℚ A] in
lemma diagF_self {M N : Bounded A} (d : ∀ n, M.X n ⟶ N.X n) (n : ℤ) : diagF d n n = d n := by
  simp [diagF]

omit [Linear ℚ A] in
lemma diagF_ne {M N : Bounded A} (d : ∀ n, M.X n ⟶ N.X n) {m n : ℤ} (h : m ≠ n) :
    diagF d m n = 0 := by
  simp [diagF, h]

lemma diagF_mem {M N : Bounded A} (d : ∀ n, M.X n ⟶ N.X n) : diagF d ∈ homSub M N :=
  ⟨0, fun m n h => diagF_ne d (by intro e; subst e; simp at h)⟩

omit [Linear ℚ A] in
lemma diagF_compF {M N P : Bounded A} (d : ∀ n, M.X n ⟶ N.X n) (g : ∀ m n : ℤ, N.X n ⟶ P.X m)
    (l n : ℤ) : compF (diagF d) g l n = d n ≫ g l n := by
  rw [compF, finsum_eq_single _ n (fun m hm => by rw [diagF_ne d hm, zero_comp]), diagF_self]

omit [Linear ℚ A] in
lemma compF_diagF {M N P : Bounded A} (f : ∀ m n : ℤ, M.X n ⟶ N.X m) (e : ∀ n, N.X n ⟶ P.X n)
    (l n : ℤ) : compF f (diagF e) l n = f l n ≫ e l := by
  rw [compF, finsum_eq_single _ l (fun m hm => by rw [diagF_ne e (Ne.symm hm), comp_zero]),
    diagF_self]

instance : Category.{v} (Bounded A) where
  Hom M N := homSub M N
  id M := ⟨diagF fun n => 𝟙 (M.X n), diagF_mem _⟩
  comp f g := ⟨compF f.1 g.1, compF_mem f.2 g.2⟩
  id_comp f := Subtype.ext <| funext₂ fun l n => by
    dsimp only
    rw [diagF_compF, Category.id_comp]
  comp_id f := Subtype.ext <| funext₂ fun l n => by
    dsimp only
    rw [compF_diagF, Category.comp_id]
  assoc {M N P Q} f g h := Subtype.ext <| funext₂ fun l n => by
    obtain ⟨r, hr⟩ := f.2
    obtain ⟨s, hs⟩ := g.2
    dsimp only
    have key : ∀ k ∉ Finset.Icc (n - ↑(r + s)) (n + ↑(r + s)), compF f.1 g.1 k n = 0 :=
      fun k hk => compF_eq_zero hr hs (lt_abs_of_not_mem hk)
    rw [compF_eq_sum _ _ l n (Finset.Icc (n - ↑(r + s)) (n + ↑(r + s)))
      (fun k hk => by rw [key k hk, zero_comp])]
    rw [compF_eq_sum _ _ l n (Finset.Icc (n - r) (n + r))
      (fun m hm => by rw [hr m n (lt_abs_of_not_mem hm), zero_comp])]
    have e1 : ∀ k, compF f.1 g.1 k n ≫ h.1 l k =
        ∑ m ∈ Finset.Icc (n - r) (n + r), f.1 m n ≫ g.1 k m ≫ h.1 l k := fun k => by
      rw [compF_eq_sum f.1 g.1 k n (Finset.Icc (n - r) (n + r))
        (fun m hm => by rw [hr m n (lt_abs_of_not_mem hm), zero_comp]), Preadditive.sum_comp]
      simp only [Category.assoc]
    simp_rw [e1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.mem_Icc] at hm
    rw [compF_eq_sum g.1 h.1 l m (Finset.Icc (n - ↑(r + s)) (n + ↑(r + s))) (fun k hk => by
      have : (s : ℤ) < |k - m| := by
        have := lt_abs_of_not_mem hk
        rw [lt_abs] at this ⊢
        push_cast at this
        omega
      rw [hs k m this, zero_comp]), Preadditive.comp_sum]

variable {M N P : Bounded A}

lemma comp_apply (f : M ⟶ N) (g : N ⟶ P) (l n : ℤ) : (f ≫ g).1 l n = compF f.1 g.1 l n := rfl

@[ext]
lemma hom_ext {f g : M ⟶ N} (h : ∀ m n, f.1 m n = g.1 m n) : f = g :=
  Subtype.ext (funext₂ h)

private lemma exists_window {f : ∀ m n : ℤ, M.X n ⟶ N.X m} (hf : f ∈ homSub M N) (n : ℤ) :
    ∃ s : Finset ℤ, ∀ m ∉ s, f m n = 0 := by
  obtain ⟨r, hr⟩ := hf
  exact ⟨Finset.Icc (n - r) (n + r), fun m hm => hr m n (lt_abs_of_not_mem hm)⟩

instance : Preadditive (Bounded A) where
  homGroup M N := inferInstanceAs (AddCommGroup (homSub M N))
  add_comp M N P f f' g := hom_ext fun l n => by
    obtain ⟨s, hs⟩ := exists_window f.2 n
    obtain ⟨s', hs'⟩ := exists_window f'.2 n
    have h1 : ∀ m ∉ s ∪ s', f.1 m n = 0 := fun m hm => hs m (by simp_all)
    have h2 : ∀ m ∉ s ∪ s', f'.1 m n = 0 := fun m hm => hs' m (by simp_all)
    change compF (f.1 + f'.1) g.1 l n = compF f.1 g.1 l n + compF f'.1 g.1 l n
    rw [compF_eq_sum _ _ l n (s ∪ s') (fun m hm => by simp [h1 m hm, h2 m hm]),
      compF_eq_sum _ _ l n (s ∪ s') (fun m hm => by simp [h1 m hm]),
      compF_eq_sum _ _ l n (s ∪ s') (fun m hm => by simp [h2 m hm]), ← Finset.sum_add_distrib]
    simp
  comp_add M N P f g g' := hom_ext fun l n => by
    obtain ⟨s, hs⟩ := exists_window f.2 n
    change compF f.1 (g.1 + g'.1) l n = compF f.1 g.1 l n + compF f.1 g'.1 l n
    rw [compF_eq_sum _ _ l n s (fun m hm => by simp [hs m hm]),
      compF_eq_sum _ _ l n s (fun m hm => by simp [hs m hm]),
      compF_eq_sum _ _ l n s (fun m hm => by simp [hs m hm]), ← Finset.sum_add_distrib]
    simp

lemma add_apply (f g : M ⟶ N) (m n : ℤ) : (f + g).1 m n = f.1 m n + g.1 m n := rfl

lemma zero_apply (m n : ℤ) : (0 : M ⟶ N).1 m n = 0 := rfl

lemma sum_apply {ι : Type*} (s : Finset ι) (f : ι → (M ⟶ N)) (m n : ℤ) :
    (∑ i ∈ s, f i).1 m n = ∑ i ∈ s, (f i).1 m n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [zero_apply]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, add_apply, ih]

instance : Linear ℚ (Bounded A) where
  homModule M N := inferInstanceAs (Module ℚ (homSub M N))
  smul_comp M N P c f g := hom_ext fun l n => by
    obtain ⟨s, hs⟩ := exists_window f.2 n
    change compF (c • f.1) g.1 l n = c • compF f.1 g.1 l n
    rw [compF_eq_sum _ _ l n s (fun m hm => by simp [hs m hm]),
      compF_eq_sum _ _ l n s (fun m hm => by simp [hs m hm]), Finset.smul_sum]
    simp
  comp_smul M N P f c g := hom_ext fun l n => by
    obtain ⟨s, hs⟩ := exists_window f.2 n
    change compF f.1 (c • g.1) l n = c • compF f.1 g.1 l n
    rw [compF_eq_sum _ _ l n s (fun m hm => by simp [hs m hm]),
      compF_eq_sum _ _ l n s (fun m hm => by simp [hs m hm]), Finset.smul_sum]
    simp

lemma smul_apply (c : ℚ) (f : M ⟶ N) (m n : ℤ) : (c • f).1 m n = c • f.1 m n := rfl

/-- The diagonal morphism with entries `d n : M_n ⟶ N_n`, of propagation `0`. -/
def diag (d : ∀ n, M.X n ⟶ N.X n) : M ⟶ N := ⟨diagF d, diagF_mem d⟩

lemma diag_apply (d : ∀ n, M.X n ⟶ N.X n) (m n : ℤ) : (diag d).1 m n = diagF d m n := rfl

lemma id_eq_diag (M : Bounded A) : 𝟙 M = diag fun n => 𝟙 (M.X n) := rfl

lemma diag_comp_diag (d : ∀ n, M.X n ⟶ N.X n) (e : ∀ n, N.X n ⟶ P.X n) :
    diag d ≫ diag e = diag fun n => d n ≫ e n := hom_ext fun l n => by
  show compF (diagF d) (diagF e) l n = diagF (fun n => d n ≫ e n) l n
  rw [diagF_compF]
  by_cases h : l = n
  · subst h; rw [diagF_self, diagF_self]
  · rw [diagF_ne _ h, diagF_ne _ h, comp_zero]

lemma diag_zero : diag (fun n => (0 : M.X n ⟶ N.X n)) = 0 := hom_ext fun m n => by
  rw [diag_apply, zero_apply]
  by_cases h : m = n
  · subst h; rw [diagF_self]
  · rw [diagF_ne _ h]

lemma sum_diag {ι : Type*} (s : Finset ι) (d : ι → ∀ n, M.X n ⟶ N.X n) :
    ∑ i ∈ s, diag (d i) = diag fun n => ∑ i ∈ s, d i n := hom_ext fun m n => by
  rw [sum_apply]
  simp only [diag_apply]
  by_cases h : m = n
  · subst h; simp only [diagF_self]
  · simp only [diagF_ne _ h, Finset.sum_const_zero]

section Biproducts

variable [HasFiniteBiproducts A]

/-- The degreewise biproduct bicone of a finite family of objects of `C_ℤ(A)`. -/
def biconeOf {J : Type} [Fintype J] [DecidableEq J] (F : J → Bounded A) : Bicone F where
  pt := ⟨fun n => ⨁ fun j => (F j).X n⟩
  π j := diag fun n => biproduct.π (fun j => (F j).X n) j
  ι j := diag fun n => biproduct.ι (fun j => (F j).X n) j
  ι_π j j' := by
    rw [diag_comp_diag]
    by_cases h : j = j'
    · subst h
      simp only [biproduct.ι_π_self, dite_true, eqToHom_refl]
      rfl
    · simp only [biproduct.ι_π_ne _ h, h, dite_false]
      exact diag_zero

lemma biconeOf_total {J : Type} [Fintype J] [DecidableEq J] (F : J → Bounded A) :
    ∑ j, (biconeOf F).π j ≫ (biconeOf F).ι j = 𝟙 (biconeOf F).pt := by
  have h : ∀ j, (biconeOf F).π j ≫ (biconeOf F).ι j =
      diag (M := (biconeOf F).pt) (N := (biconeOf F).pt)
        (fun n => biproduct.π (fun j => (F j).X n) j ≫ biproduct.ι (fun j => (F j).X n) j) :=
    fun j => diag_comp_diag _ _
  rw [Finset.sum_congr rfl (fun j _ => h j), sum_diag, id_eq_diag]
  congr 1
  funext n
  exact biproduct.total

instance : HasFiniteBiproducts (Bounded A) where
  out _ := ⟨fun F => HasBiproduct.mk ⟨biconeOf F, isBilimitOfTotal _ (biconeOf_total F)⟩⟩

end Biproducts

end Bounded

end HSP

end
