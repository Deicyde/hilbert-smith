import HilbertSmithPaper.LTheory.Bounded.Categories.BoundedCategory
import HilbertSmithPaper.LTheory.Bounded.Categories.BoundedDuality

/-!
# Diagonal morphisms of `C_ℤ(A)`

For maps `d_n : M_n ⟶ N_n`, `diag(d) : M ⟶ N` has entries `d_n` at `(n, n)` and `0` elsewhere
(propagation `0`); `diag(e) diag(d) = diag(e_n d_n)`, the zero family gives `0`,
`1_M = diag(1_{M_n})`, `diag(d) + diag(d') = diag(d_n + d'_n)` and `diag(d)^* = diag(d_n^*)`;
for isomorphisms `e_n`, `diag(e)` is an isomorphism with inverse `diag(e_n^{-1})`.

## Encoding

`Bounded.diag d` (the declaration of the article) is the bounded family `Bounded.diagF d`; the
lemmas `diag_apply`, `diag_comp_diag`, `diag_zero`, `id_eq_diag`, `diag_add` and `dualHom_diag_eq`
unfold it, and `Bounded.diagIso e` bundles `diag` of a family of isomorphisms as an isomorphism.
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace HSP

universe v u

namespace Bounded

variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℚ A] {M N P : Bounded A}

/-- The diagonal morphism with entries `d n : M_n ⟶ N_n`, of propagation `0`. -/
def diag (d : ∀ n, M.X n ⟶ N.X n) : M ⟶ N :=
  ⟨diagF d, ⟨0, fun _ _ h => diagF_ne d (by intro e; subst e; simp at h)⟩⟩

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


lemma diag_add (d e : ∀ n, M.X n ⟶ N.X n) : diag d + diag e = diag fun n => d n + e n :=
  hom_ext fun a b => by
    rw [add_apply, diag_apply, diag_apply, diag_apply]
    by_cases h : a = b
    · subst h
      rw [diagF_self, diagF_self, diagF_self]
    · rw [diagF_ne _ h, diagF_ne _ h, diagF_ne _ h, add_zero]

/-- The diagonal isomorphism with entries `e n : M_n ≅ N_n`: `diag (e n).hom`, with inverse
`diag (e n).inv`. -/
def diagIso (e : ∀ n, M.X n ≅ N.X n) : M ≅ N where
  hom := diag fun n => (e n).hom
  inv := diag fun n => (e n).inv
  hom_inv_id := by rw [diag_comp_diag]; simp only [Iso.hom_inv_id]; rfl
  inv_hom_id := by rw [diag_comp_diag]; simp only [Iso.inv_hom_id]; rfl

open DualCat in
lemma dualHom_diag_eq [HasFiniteBiproducts A] [DualCat A] (d : ∀ n, M.X n ⟶ N.X n) :
    dualHom (diag d) = diag (M := dual N) (N := dual M) (fun n => dualHom (d n)) :=
  hom_ext fun a b => by
    rw [dualHom_apply]
    change dualHom (diagF d b a) = diagF (M := dual N) (N := dual M) (fun n => dualHom (d n)) a b
    by_cases h : a = b
    · subst h
      rw [diagF_self, diagF_self]
    · rw [diagF_ne _ (Ne.symm h), diagF_ne _ h, dualHom_zero]

end Bounded

end HSP

end
