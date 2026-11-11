import HilbertSmithPaper.LTheory.Bounded.Categories.BoundedCategory

/-!
# Diagonal morphisms of `C_ℤ(A)`

For maps `d_n : M_n ⟶ N_n`, `diag(d) : M ⟶ N` has entries `d_n` at `(n, n)` and `0` elsewhere
(propagation `0`); `diag(e) diag(d) = diag(e_n d_n)`, the zero family gives `0`, and
`1_M = diag(1_{M_n})`.

## Encoding

`Bounded.diag d` (the declaration of the article) is the bounded family `Bounded.diagF d`; the
lemmas `diag_apply`, `diag_comp_diag`, `diag_zero` and `id_eq_diag` unfold it.
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

end Bounded

end HSP

end
