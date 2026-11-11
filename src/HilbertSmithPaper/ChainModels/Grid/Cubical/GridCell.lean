import Mathlib
import HilbertSmithPaper.ChainModels.Grid.Cubical.CubicalTorusGrid
import HilbertSmithPaper.ChainModels.Grid.Cubical.GridCube
import HilbertSmithPaper.ChainModels.Grid.Cubical.CircleCell
import HilbertSmithPaper.ChainModels.Grid.Cubical.GridCubeDim

/-!
# The cube of a basis vector

The basis vector `x ⊗ y` of the summand `C(k)_p ⊠ S_{k,r-p}` of `(C(k) ⊗ S_k)_r` has the cube of
`x` followed by the cell of `y`.

## Encoding

`gridCell k n r a` (the declaration of the article), by recursion on `n`. The private lemmas
`gridCell_dim`, `gridCell_injective` and `gridCell_surjective` check that the basis vectors of
`C(k)_r` are the cubes of dimension `r` (not part of the article).
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP.ChainModels

open FreeQ

/-- The cube of a basis vector of `C(k)_r`: the basis vector `x ⊗ y` of the summand
`C(k)_p ⊠ S_{k,r-p}` of `C(k) ⊗ S_k` has the cube of `x` followed by the cell of `y`. -/
noncomputable def gridCell (k : ℕ) : ∀ (n : ℕ) (r : ℤ), Fin ((gridComplex k n).X r).dim → GridCube k n
  | 0, _, _ => finZeroElim
  | n + 1, r, a =>
    let s := finSigmaFinEquiv.symm a
    let ij := finProdFinEquiv.symm s.2
    Fin.snoc (gridCell k n ((s.1 : ℕ) : ℤ) ij.1) (circleCell k (r - (s.1 : ℕ)) ij.2)

/-! ### The basis of `C(k)` consists of the cubes -/

private lemma circleCell_cast (k : ℕ) {q q' : ℤ} (h : q = q') (j : Fin ((circleComplex k).X q).dim) :
    circleCell k q' (Fin.cast (by rw [h]) j) = circleCell k q j := by
  subst h; rfl

private lemma circleCell_spec (k : ℕ) (q : ℤ) (j : Fin ((circleComplex k).X q).dim) :
    (q = 0 ∧ (circleCell k q j).2 = false) ∨ (q = 1 ∧ (circleCell k q j).2 = true) := by
  rcases q with (_ | _ | q) | q
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩
  · exact j.elim0
  · exact j.elim0

private lemma circleCell_injective (k : ℕ) (q : ℤ) : Function.Injective (circleCell k q) := by
  intro j j' h
  rcases q with (_ | _ | q) | q
  · exact congrArg Prod.fst h
  · exact congrArg Prod.fst h
  · exact j.elim0
  · exact j.elim0

private lemma dim_snoc {k n : ℕ} (c : GridCube k n) (b : Fin k × Bool) :
    GridCube.dim (Fin.snoc c b : GridCube k (n + 1)) = c.dim + if b.2 then 1 else 0 := by
  simp only [GridCube.dim, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]

private lemma gridCell_succ_mk (k n : ℕ) (r : ℤ) (p : Fin (r.toNat + 1))
    (i : Fin ((gridComplex k n).X (p : ℕ)).dim) (j : Fin ((circleComplex k).X (r - (p : ℕ))).dim) :
    gridCell k (n + 1) r (finSigmaFinEquiv ⟨p, finProdFinEquiv (i, j)⟩) =
      Fin.snoc (gridCell k n (p : ℕ) i) (circleCell k (r - (p : ℕ)) j) := by
  have e1 := congrArg (fun s : (q : Fin (r.toNat + 1)) ×
      Fin (tensorSummandDim (gridComplex k n) (circleComplex k) r q) =>
      (Fin.snoc (gridCell k n (s.1 : ℕ) (finProdFinEquiv.symm s.2).1)
        (circleCell k (r - (s.1 : ℕ)) (finProdFinEquiv.symm s.2).2) : GridCube k (n + 1)))
    (finSigmaFinEquiv.symm_apply_apply ⟨p, finProdFinEquiv (i, j)⟩)
  refine e1.trans ?_
  exact congrArg (fun ij : Fin ((gridComplex k n).X (p : ℕ)).dim ×
      Fin ((circleComplex k).X (r - (p : ℕ))).dim =>
      (Fin.snoc (gridCell k n (p : ℕ) ij.1) (circleCell k (r - (p : ℕ)) ij.2) : GridCube k (n + 1)))
    (finProdFinEquiv.symm_apply_apply (i, j))

/-- The cube of a basis vector of `C(k)_r` has dimension `r`. -/
private lemma gridCell_dim (k : ℕ) : ∀ (n : ℕ) (r : ℤ) (a : Fin ((gridComplex k n).X r).dim),
    ((gridCell k n r a).dim : ℤ) = r
  | 0, r, a => by
    rcases r with (_ | r) | r
    · simp [GridCube.dim]
    · exact a.elim0
    · exact a.elim0
  | n + 1, r, a => by
    obtain ⟨⟨p, x⟩, rfl⟩ := finSigmaFinEquiv.surjective a
    obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective x
    rw [gridCell_succ_mk, dim_snoc, Nat.cast_add, gridCell_dim k n]
    rcases circleCell_spec k _ j with ⟨h, h'⟩ | ⟨h, h'⟩ <;> simp only [h'] <;> push_cast <;>
      omega

/-- Distinct basis vectors of `C(k)_r` have distinct cubes. -/
private lemma gridCell_injective (k : ℕ) : ∀ (n : ℕ) (r : ℤ), Function.Injective (gridCell k n r)
  | 0, r, a, a', _ => by
    rcases r with (_ | r) | r
    · exact Subsingleton.elim (α := Fin 1) a a'
    · exact a.elim0
    · exact a.elim0
  | n + 1, r, a, a', h => by
    obtain ⟨⟨p, x⟩, rfl⟩ := finSigmaFinEquiv.surjective a
    obtain ⟨⟨p', x'⟩, rfl⟩ := finSigmaFinEquiv.surjective a'
    obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective x
    obtain ⟨⟨i', j'⟩, rfl⟩ := finProdFinEquiv.surjective x'
    rw [gridCell_succ_mk, gridCell_succ_mk] at h
    have hi := congrArg Fin.init h
    have hj := congrArg (fun c => c (Fin.last n)) h
    simp only [Fin.init_snoc, Fin.snoc_last] at hi hj
    have hp : p = p' := by
      have := congrArg (fun c => (GridCube.dim c : ℤ)) hi
      simp only [gridCell_dim] at this
      exact Fin.ext (by exact_mod_cast this)
    subst hp
    rw [gridCell_injective k n _ hi, circleCell_injective k _ hj]

/-- Every cube of dimension `r` is the cube of a basis vector of `C(k)_r`. -/
private lemma gridCell_surjective (k : ℕ) : ∀ (n : ℕ) (r : ℤ) (c : GridCube k n), (c.dim : ℤ) = r →
    ∃ a, gridCell k n r a = c
  | 0, r, c, h => by
    have hr : r = 0 := by rw [← h]; simp [GridCube.dim]
    subst hr
    exact ⟨⟨0, Nat.one_pos⟩, funext fun j => j.elim0⟩
  | n + 1, r, c, h => by
    obtain ⟨p, hpdef⟩ : ∃ p, GridCube.dim (Fin.init c) = p := ⟨_, rfl⟩
    obtain ⟨i, hi⟩ := gridCell_surjective k n (p : ℤ) (Fin.init c) (by rw [hpdef])
    set b := c (Fin.last n)
    have hc : (Fin.snoc (Fin.init c) b : GridCube k (n + 1)) = c := Fin.snoc_init_self c
    have hdim : (c.dim : ℤ) = p + if b.2 then 1 else 0 := by
      rw [← hc, dim_snoc, hpdef]; push_cast; rfl
    set q : ℤ := if b.2 then 1 else 0
    have hq : r - (p : ℕ) = q := by omega
    have hp : p < r.toNat + 1 := by
      have : (0 : ℤ) ≤ q := by simp only [q]; split_ifs <;> norm_num
      omega
    let j : Fin ((circleComplex k).X q).dim := Fin.cast (by simp only [q]; split_ifs <;> rfl) b.1
    have hj : circleCell k q j = b := by
      simp only [j, q]
      rcases b with ⟨w, _ | _⟩ <;> rfl
    refine ⟨finSigmaFinEquiv ⟨⟨p, hp⟩, finProdFinEquiv (i, Fin.cast (by rw [hq]) j)⟩, ?_⟩
    rw [gridCell_succ_mk, ← hc]
    simp only [Fin.val_mk]
    congr 1
    rw [circleCell_cast k hq.symm, hj]

end HSP.ChainModels
