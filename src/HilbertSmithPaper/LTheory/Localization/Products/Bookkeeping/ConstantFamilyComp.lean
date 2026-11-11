import Mathlib
import HilbertSmithPaper.LTheory.Bounded.Categories.BoundedCategory
import HilbertSmithPaper.LTheory.Localization.Products.BasedVectorSpaces

/-!
# Entries of composites of constant families

In `C_ℤ(ℚ)`, let `f : M ⟶ N` and `g : N ⟶ P` have components `f_{mn}`, `g_{lm}` whose matrices
have all entries equal to `c(m, n)` and `c'(l, m)`, with `c(m, n) = 0` for `|m - n| > 1`. Then
every entry of `(g f)_{ln}` is `∑_{m=n-1}^{n+1} d_m c'(l, m) c(m, n)`, where `d_m` is the
dimension of `N` in position `m`.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

private lemma sum_entry {X Y : FreeQ} (s : Finset ℤ) (F : ℤ → (X ⟶ Y)) (i : Fin Y.dim)
    (j : Fin X.dim) : FreeQ.toMatrix (∑ m ∈ s, F m) i j = ∑ m ∈ s, FreeQ.toMatrix (F m) i j :=
  map_sum (⟨⟨fun f : X ⟶ Y => FreeQ.toMatrix f i j, rfl⟩, fun _ _ => rfl⟩ : (X ⟶ Y) →+ ℚ) F s

private lemma ofMatrix_const_eq_zero {X Y : FreeQ} {c : ℚ} (h : c = 0) :
    (FreeQ.ofMatrix fun _ _ => c : X ⟶ Y) = 0 := by
  change (fun _ _ => c : Matrix _ _ ℚ) = 0
  ext
  simp [h]

/-- **Entries of composites of constant families.** The entries of a composite of
constant-matrix families of propagation `≤ 1`. -/
lemma constFamily_comp_entry {M N P : Bounded FreeQ} (f : M ⟶ N) (g : N ⟶ P) (c c' : ℤ → ℤ → ℚ)
    (hf : ∀ m n, f.1 m n = FreeQ.ofMatrix fun _ _ => c m n)
    (hg : ∀ m n, g.1 m n = FreeQ.ofMatrix fun _ _ => c' m n)
    (hc : ∀ m n, 1 < |m - n| → c m n = 0) (l n : ℤ) (i : Fin (P.X l).dim)
    (j : Fin (M.X n).dim) :
    FreeQ.toMatrix ((f ≫ g).1 l n) i j =
      ∑ m ∈ Finset.Icc (n - 1) (n + 1), ((N.X m).dim : ℚ) * (c' l m * c m n) := by
  rw [Bounded.comp_apply, Bounded.compF_eq_sum _ _ l n (Finset.Icc (n - 1) (n + 1))
    (fun m hm => by
      rw [Finset.mem_Icc] at hm
      rw [hf, ofMatrix_const_eq_zero (hc m n (by rw [lt_abs]; omega)), zero_comp]), sum_entry]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [hf, hg]
  change ∑ k : Fin (N.X m).dim, c' l m * c m n = _
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end HSP
