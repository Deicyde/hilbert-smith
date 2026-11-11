import Mathlib
import HilbertSmithPaper.ChainModels.Grid.Torus
import HilbertSmithPaper.ChainModels.Grid.BasedComplexTensor
import HilbertSmithPaper.LTheory.Localization.Products.BasedVectorSpaces
import HilbertSmithPaper.LTheory.Localization.Products.BasedTensor

/-!
# Cubical torus grid

The circle complex `S_k` (cells `[w]` in degree `0`, `e_w` in degree `1`, `w ∈ ℤ/k`,
`d e_w = [w+1] - [w]`, `ε[w] = 1`), its realizations on `ℝ/4ℤ`, and the grid complex
`C(k) = S_k^{⊗n}` on the torus `𝕋ⁿ`, whose basis vectors are the cubes `c = b_1 ⊗ ⋯ ⊗ b_n`,
with closed cubes, centers, closed stars, the fundamental chain and subcomplexes.

## Encoding

* Complexes are `ChainComplex FreeQ ℤ` (based vector spaces). `ℤ/k` is `Fin k` with addition
  mod `k`; a cell of `S_k` is a pair `(w, b) : Fin k × Bool`, `b = true` for the edge `e_w`.
* The cells of degree `r` are enumerated in the order written: `[0], …, [k-1]` and
  `e_0, …, e_{k-1}`; `circleCell` reads a basis vector of `S_{k,r}` as a cell.
* `gridComplex k n` is `C(k)` in dimension `n`: the iterated tensor product of based complexes
  `(⋯((𝟙 ⊗ S_k) ⊗ S_k) ⊗ ⋯) ⊗ S_k` starting from the unit complex `𝟙` (`ℚ` in degree `0`);
  tensoring with `𝟙` on the left changes neither the complex nor its bases.
* A cube `c = (w, S)` is a function `Fin n → Fin k × Bool` (`j ∈ S` iff the `j`-th factor is an
  edge); `gridCell` reads a basis vector of `C(k)_r` as its cube.
* The augmentation `ε^{⊗n}` and the fundamental chain `z(k)` are morphisms from and to
  `ℚ = ⟨1⟩`: a row of ones, and the column `⊗_j ∑_w e_w`.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP.ChainModels

open FreeQ

/-! ### The circle complex -/

/-- The number of cells of `S_k` in degree `r`: `k` in degrees `0` and `1`, and `0` otherwise. -/
def circleDim (k : ℕ) : ℤ → ℕ
  | .ofNat 0 => k
  | .ofNat 1 => k
  | _ => 0

/-- The differential `d e_w = [w+1] - [w]` of `S_k`, as a `k × k` matrix (rows `[a]`, columns
`e_b`). -/
def circleDiffMatrix (k : ℕ) : Matrix (Fin k) (Fin k) ℚ :=
  Matrix.of fun a b =>
    (if (a : ℕ) = ((b : ℕ) + 1) % k then 1 else 0) - (if a = b then 1 else 0)

/-- The differential of `S_k` out of degree `n + 1`: the matrix above for `n = 0`, else `0`. -/
def circleD (k : ℕ) : ∀ n : ℤ, (⟨circleDim k (n + 1)⟩ : FreeQ) ⟶ ⟨circleDim k n⟩
  | .ofNat 0 => ofMatrix (circleDiffMatrix k)
  | .ofNat (_ + 1) => 0
  | .negSucc _ => 0

private lemma circleD_ne (k : ℕ) {n : ℤ} (h : n ≠ 0) : circleD k n = 0 := by
  rcases n with (_ | m) | m
  · exact absurd rfl h
  · rfl
  · rfl

/-- The *circle complex* `S_k`. -/
def circleComplex (k : ℕ) : ChainComplex FreeQ ℤ :=
  ChainComplex.of (fun r => ⟨circleDim k r⟩) (circleD k) fun n => by
    by_cases h : n = 0
    · subst h
      exact (congrArg (· ≫ circleD k 0) (circleD_ne k (show (0 : ℤ) + 1 ≠ 0 by decide))).trans
        zero_comp
    · rw [circleD_ne k h, comp_zero]

lemma circleComplex_X (k : ℕ) (r : ℤ) : (circleComplex k).X r = ⟨circleDim k r⟩ := rfl

lemma circleComplex_d (k : ℕ) : (circleComplex k).d 1 0 = ofMatrix (circleDiffMatrix k) :=
  ChainComplex.of_d (fun r => (⟨circleDim k r⟩ : FreeQ)) (circleD k) (0 : ℤ)

lemma circleComplex_dim_neg (k : ℕ) : ∀ q < 0, ((circleComplex k).X q).dim = 0 := by
  intro q hq
  rcases q with q | q
  · exact absurd hq (by simp)
  · rfl

/-- The augmentation `ε[w] = 1` of `S_k`, a row of ones. -/
def circleAug (k : ℕ) : (circleComplex k).X 0 ⟶ (⟨1⟩ : FreeQ) :=
  ofMatrix (Matrix.of fun _ _ => 1)

/-- The cell `[w]` (for `r = 0`) or `e_w` (for `r = 1`) of the `w`-th basis vector of `S_{k,r}`. -/
def circleCell (k : ℕ) : ∀ r : ℤ, Fin ((circleComplex k).X r).dim → Fin k × Bool
  | .ofNat 0, w => (w, false)
  | .ofNat 1, w => (w, true)
  | .ofNat (_ + 2), w => w.elim0
  | .negSucc _, w => w.elim0

/-- The realization of a cell of `S_k`: the point `4w/k`, or the arc from `4w/k` to
`4(w+1)/k`. -/
def cellRealization (k : ℕ) (b : Fin k × Bool) : Set (AddCircle (4 : ℝ)) :=
  if b.2 then (fun t : ℝ => (t : AddCircle (4 : ℝ))) ''
      Set.Icc (4 * (b.1 : ℕ) / k : ℝ) (4 * ((b.1 : ℕ) + 1) / k)
  else {((4 * (b.1 : ℕ) / k : ℝ) : AddCircle (4 : ℝ))}

/-! ### The grid complex -/

/-- The number of cells of the unit complex `𝟙` in degree `r`: `1` in degree `0`, else `0`. -/
def unitDim : ℤ → ℕ
  | .ofNat 0 => 1
  | _ => 0

/-- The unit complex `𝟙`: `ℚ` in degree `0`. -/
def unitComplex : ChainComplex FreeQ ℤ :=
  ChainComplex.of (fun r => ⟨unitDim r⟩) (fun _ => 0) fun _ => zero_comp

/-- The *grid complex* `C(k) = S_k^{⊗n}`: the iterated tensor product of based complexes
`(⋯((𝟙 ⊗ S_k) ⊗ S_k) ⊗ ⋯) ⊗ S_k` with `n` factors `S_k`. -/
noncomputable def gridComplex (k : ℕ) : ℕ → ChainComplex FreeQ ℤ
  | 0 => unitComplex
  | n + 1 => basedComplexTensor (gridComplex k n) (circleComplex k) (circleComplex_dim_neg k)

/-- A *cube* `c = (w, S)` of the grid: for each coordinate `j` the cell `b_j = (w_j, j ∈ S)` of
`S_k`. -/
abbrev GridCube (k n : ℕ) : Type := Fin n → Fin k × Bool

/-- The dimension `|S|` of a cube: the number of its edge coordinates. -/
def GridCube.dim {k n : ℕ} (c : GridCube k n) : ℕ :=
  ∑ j, if (c j).2 then 1 else 0

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
lemma gridCell_dim (k : ℕ) : ∀ (n : ℕ) (r : ℤ) (a : Fin ((gridComplex k n).X r).dim),
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
lemma gridCell_injective (k : ℕ) : ∀ (n : ℕ) (r : ℤ), Function.Injective (gridCell k n r)
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
lemma gridCell_surjective (k : ℕ) : ∀ (n : ℕ) (r : ℤ) (c : GridCube k n), (c.dim : ℤ) = r →
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

/-- The closed cube `|c| ⊆ 𝕋ⁿ`, the product of the realizations of its cells. -/
def GridCube.realization {k n : ℕ} (c : GridCube k n) : Set (Torus n) :=
  Set.pi Set.univ fun j => cellRealization k (c j)

/-- The center `x_c` of a cube: `4w_j/k`, plus `2/k` in the edge coordinates. -/
noncomputable def GridCube.center {k n : ℕ} (c : GridCube k n) : Torus n :=
  fun j => ((4 * ((c j).1 : ℕ) + if (c j).2 then 2 else 0) / k : ℝ)

/-- The closed star `st(c)`: the union of the closed cubes containing `|c|`. -/
def GridCube.closedStar {k n : ℕ} (c : GridCube k n) : Set (Torus n) :=
  ⋃ (c' : GridCube k n) (_ : c.realization ⊆ c'.realization), c'.realization

/-- The two faces of a cube in an edge coordinate `j`: `[w_j]` and `[w_j + 1]` replace `e_{w_j}`. -/
def GridCube.face {k n : ℕ} (c : GridCube k n) (j : Fin n) (top : Bool) : GridCube k n :=
  Function.update c j
    (if top then ⟨((c j).1 + 1 : ℕ) % k, Nat.mod_lt _ (Fin.pos (c j).1)⟩ else (c j).1, false)

/-- A *subcomplex*: a set of cubes closed under taking faces (its span is the subcomplex). -/
def IsGridSubcomplex {k n : ℕ} (s : Set (GridCube k n)) : Prop :=
  ∀ c ∈ s, ∀ j, (c j).2 = true → ∀ top, c.face j top ∈ s

/-- The augmentation `ε^{⊗n} : C(k)_0 → ℚ`: on the unique summand `C(k)_0 ⊠ S_{k,0}` of
`(C(k) ⊗ S_k)_0`, the Kronecker product of the augmentations. -/
noncomputable def gridAug (k : ℕ) : ∀ n : ℕ, (gridComplex k n).X 0 ⟶ (⟨1⟩ : FreeQ)
  | 0 => ofMatrix (Matrix.of fun _ _ => 1)
  | n + 1 => blockProj _ (0 : Fin 1) ≫ basedKron (gridAug k n) (circleAug k)

/-- The fundamental chain of `S_k`, `∑_w e_w`, as a column. -/
def circleFundamental (k : ℕ) : (⟨1⟩ : FreeQ) ⟶ (circleComplex k).X 1 :=
  ofMatrix (Matrix.of fun _ _ => 1)

/-- The *fundamental chain* `z(k) = ⊗_j ∑_w e_w ∈ C(k)_n`, as a column: in `(C(k) ⊗ S_k)_{n+1}`
it lies in the summand `C(k)_n ⊠ S_{k,1}`. -/
noncomputable def gridFundamental (k : ℕ) : ∀ n : ℕ, (⟨1⟩ : FreeQ) ⟶ (gridComplex k n).X n
  | 0 => ofMatrix (Matrix.of fun _ _ => 1)
  | n + 1 =>
    basedKron (gridFundamental k n)
        (circleFundamental k ≫ eqToHom (congrArg (circleComplex k).X (by push_cast; ring))) ≫
      blockInc (tensorSummandDim (gridComplex k n) (circleComplex k) ((n + 1 : ℕ) : ℤ))
        ⟨n, by simp⟩

end HSP.ChainModels
