import Mathlib
import HilbertSmithPaper.LTheory.Base.Categories.DualityCategory

/-!
# The bounded category `C_ℤ(A)`

For a ℚ-linear additive category `A`, an object of `C_ℤ(A)` is a family `M = (M_n)_{n ∈ ℤ}` of
objects of `A`; a morphism `f : M → N` is a family `f_{mn} : M_n → N_m` with bounded propagation
(some `r ≥ 0` with `f_{mn} = 0` whenever `|m - n| > r`). Composition is the matrix product
`(gf)_{ln} = ∑_m g_{lm} f_{mn}`, a finite sum; biproducts are taken degreewise.

## Encoding

* `Bounded A` is a type synonym for `ℤ → A`; `Bounded.Hom M N` is the structure of a family
  `f m n : M n ⟶ N m` with an existential propagation bound.
* Composition (in diagrammatic order `f ≫ g`) is `(f ≫ g)_{ln} = ∑ᶠ m, f_{mn} ≫ g_{lm}`; the
  `finsum` has finite support, and `Bounded.comp_f_eq_sum` computes it over any finite window
  containing the support.
* `Bounded.diag φ` is the diagonal morphism of a degreewise family `φ_n : M_n ⟶ N_n`
  (propagation `0`); the identity is `diag 𝟙`, and the biproduct bicones are diagonal.
* Instances: `Category` so far. Partial work (handed over): `Preadditive` (entrywise sums),
  `Linear ℚ` (entrywise scalars) and `HasFiniteBiproducts` (degreewise biproducts of `A`) remain.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

universe v u

/-- The objects of the bounded category `C_ℤ(A)`: families `(M_n)_{n ∈ ℤ}` of objects of `A`. -/
def Bounded (A : Type u) : Type u := ℤ → A

namespace Bounded

variable {A : Type u} [Category.{v} A] [Preadditive A]

/-- A morphism `f : M → N` of `C_ℤ(A)`: a family `f_{mn} : M_n → N_m` with bounded
propagation. -/
@[ext]
structure Hom (M N : Bounded A) : Type v where
  /-- The matrix entry `f_{mn} : M_n → N_m`. -/
  f : ∀ m n : ℤ, (M n : A) ⟶ N m
  /-- Some `r ≥ 0` bounds the propagation: `f_{mn} = 0` whenever `|m - n| > r`. -/
  bounded : ∃ r : ℕ, ∀ m n : ℤ, (r : ℤ) < |m - n| → f m n = 0

variable {M N P Q : Bounded A}

private lemma mem_window {r : ℕ} {m n : ℤ} (h : ¬ (r : ℤ) < |m - n|) :
    m ∈ Finset.Icc (n - r) (n + r) := by
  rw [not_lt, abs_sub_le_iff] at h
  rw [Finset.mem_Icc]; constructor <;> linarith

/-- Composition `(f ≫ g)_{ln} = ∑_m f_{mn} ≫ g_{lm}`. -/
noncomputable def comp (f : Hom M N) (g : Hom N P) : Hom M P where
  f l n := ∑ᶠ m, f.f m n ≫ g.f l m
  bounded := by
    obtain ⟨r, hr⟩ := f.bounded
    obtain ⟨s, hs⟩ := g.bounded
    refine ⟨r + s, fun l n h => ?_⟩
    refine (finsum_congr fun m => ?_).trans finsum_zero
    by_cases hm : (r : ℤ) < |m - n|
    · rw [hr m n hm, zero_comp]
    · have : (s : ℤ) < |l - m| := by
        have h1 := abs_sub_abs_le_abs_sub (l - n) (m - n)
        rw [sub_sub_sub_cancel_right] at h1
        push_cast at h
        linarith [not_lt.1 hm]
      rw [hs l m this, comp_zero]

/-- The composite over any finite window containing the support of the summands. -/
lemma comp_f_eq_sum (f : Hom M N) (g : Hom N P) (l n : ℤ) (s : Finset ℤ)
    (hs : ∀ m, f.f m n ≫ g.f l m ≠ 0 → m ∈ s) :
    (comp f g).f l n = ∑ m ∈ s, f.f m n ≫ g.f l m :=
  finsum_eq_sum_of_support_subset _ fun m hm => hs m hm

/-- The diagonal morphism of a degreewise family `φ_n : M_n ⟶ N_n` (propagation `0`). -/
def diag (φ : ∀ n, (M n : A) ⟶ N n) : Hom M N where
  f m n := if h : m = n then φ n ≫ eqToHom (congrArg N h.symm) else 0
  bounded := ⟨0, fun m n h => by
    have hmn : m ≠ n := fun e => by subst e; simp at h
    simp [hmn]⟩

lemma diag_f_self (φ : ∀ n, (M n : A) ⟶ N n) (n : ℤ) : (diag φ).f n n = φ n := by
  simp [diag]

lemma diag_f_ne (φ : ∀ n, (M n : A) ⟶ N n) {m n : ℤ} (h : m ≠ n) : (diag φ).f m n = 0 := by
  simp [diag, h]

lemma comp_diag_f (f : Hom M N) (ψ : ∀ n, (N n : A) ⟶ P n) (l n : ℤ) :
    (comp f (diag ψ)).f l n = f.f l n ≫ ψ l := by
  rw [comp_f_eq_sum _ _ l n {l} fun m hm => ?_, Finset.sum_singleton, diag_f_self]
  rw [Finset.mem_singleton]
  by_contra h
  exact hm (by rw [diag_f_ne _ (Ne.symm h), comp_zero])

lemma diag_comp_f (φ : ∀ n, (M n : A) ⟶ N n) (g : Hom N P) (l n : ℤ) :
    (comp (diag φ) g).f l n = φ n ≫ g.f l n := by
  rw [comp_f_eq_sum _ _ l n {n} fun m hm => ?_, Finset.sum_singleton, diag_f_self]
  rw [Finset.mem_singleton]
  by_contra h
  exact hm (by rw [diag_f_ne _ h, zero_comp])

/-- The composite has entries supported where some intermediate entries are nonzero. -/
private lemma comp_f_eq_window (f : Hom M N) (g : Hom N P) {r : ℕ}
    (hr : ∀ m n : ℤ, (r : ℤ) < |m - n| → f.f m n = 0) (l n : ℤ) :
    (comp f g).f l n = ∑ m ∈ Finset.Icc (n - r) (n + r), f.f m n ≫ g.f l m :=
  comp_f_eq_sum _ _ l n _ fun m hm => mem_window fun h => hm (by rw [hr m n h, zero_comp])

private lemma comp_assoc (f : Hom M N) (g : Hom N P) (h : Hom P Q) :
    comp (comp f g) h = comp f (comp g h) := by
  obtain ⟨r, hr⟩ := f.bounded
  obtain ⟨s, hs⟩ := g.bounded
  ext l n
  set W := Finset.Icc (n - (r + s : ℕ)) (n + (r + s : ℕ))
  have hW : ∀ k m : ℤ, k ∈ Finset.Icc (n - r) (n + r) → ¬ (s : ℤ) < |m - k| → m ∈ W := by
    intro k m h1 h2
    refine mem_window fun h3 => ?_
    rw [Finset.mem_Icc] at h1
    have h4 := abs_sub_le m k n
    have h5 : |k - n| ≤ r := abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
    push_cast at h3
    linarith [not_lt.1 h2]
  have hL : (comp (comp f g) h).f l n = ∑ m ∈ W, (comp f g).f m n ≫ h.f l m := by
    refine comp_f_eq_sum _ _ l n W fun m hm => ?_
    by_contra hmW
    apply hm
    rw [comp_f_eq_window f g hr, Preadditive.sum_comp]
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [hs m k (not_not.1 fun h2 => hmW (hW k m hk h2)), comp_zero, zero_comp]
  rw [hL, comp_f_eq_window f _ hr]
  simp_rw [comp_f_eq_window f g hr, Preadditive.sum_comp, Category.assoc]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [comp_f_eq_sum g h l k W fun m hm => hW k m hk fun h2 => hm (by rw [hs m k h2, zero_comp]),
    Preadditive.comp_sum]

/-- `C_ℤ(A)` is a category: matrix composition, identity `diag 𝟙`. -/
noncomputable instance instCategory : Category.{v} (Bounded A) where
  Hom := Hom
  id M := diag fun n => 𝟙 (M n)
  comp := comp
  id_comp f := by ext l n; rw [diag_comp_f, Category.id_comp]
  comp_id f := by ext l n; rw [comp_diag_f, Category.comp_id]
  assoc f g h := comp_assoc f g h

@[ext]
lemma hom_ext {f g : M ⟶ N} (h : ∀ m n, f.f m n = g.f m n) : f = g :=
  Hom.ext (funext fun m => funext fun n => h m n)

lemma comp_f (f : M ⟶ N) (g : N ⟶ P) (l n : ℤ) : (f ≫ g).f l n = ∑ᶠ m, f.f m n ≫ g.f l m :=
  rfl

lemma id_def (M : Bounded A) : 𝟙 M = diag fun n => 𝟙 (M n) := rfl

end Bounded

end HSP
