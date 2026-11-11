import Mathlib
import HilbertSmithPaper.ChainModels.Grid.Cubical.CircleComplex
import HilbertSmithPaper.ChainModels.Grid.Cubical.CircleAug
import HilbertSmithPaper.ChainModels.Grid.Cubical.CircleFundamental
import HilbertSmithPaper.LTheory.Base.Complexes.DualComplex
import HilbertSmithPaper.LTheory.Base.Complexes.StructureComplex
import HilbertSmithPaper.LTheory.Base.Complexes.StructureInvolution
import HilbertSmithPaper.LTheory.Base.Complexes.StructureInvolutionSquare
import HilbertSmithPaper.Categories.Asymptotic.Propagation
import HilbertSmithPaper.ChainModels.Grid.Poincare.CircleData.CirclePhi
import HilbertSmithPaper.ChainModels.Grid.Poincare.CircleData.CircleH
import HilbertSmithPaper.ChainModels.Grid.Poincare.CircleData.CirclePhiSym
import HilbertSmithPaper.ChainModels.Grid.Poincare.CircleData.CircleB
import HilbertSmithPaper.ChainModels.Grid.Poincare.CircleData.CircleK
import HilbertSmithPaper.ChainModels.Grid.Poincare.CircleData.CircleKDual

/-!
# Circle duality

On `S = S_k`, the structure `φ ∈ M(S)_1` (`φ([w]^*) = e_{w-1}`, `φ(e_w^*) = [w]`), the element
`H ∈ M(S)_2` (`H(e_w^*) = e_w`, `H([w]^*) = 0`), `φ^s = φ + ½ ∂H`, the inverse `b`
(`b(e_w) = [w+1]^*`, `b([w]) = e_w^*`) and the homotopies `K = ½ H b`, `K' = ½ b H`, with their
five properties.

## Encoding

* Components are matrices between based vector spaces (the dual of `ℚ^d` is `ℚ^d`), written by
  their entries in terms of the indices `w ∈ Fin k`: `φ_{0,1}` is the identity matrix,
  `φ_{1,0}` has entry `1` at (row `e_{w-1}`, column `[w]^*`), `H_{1,1}` is the identity matrix,
  and all other components are zero (their objects are zero-dimensional).
* `circleB k r : S_r → (S^{1-*})_r` is the degree-`r` component of `b`; `circleK k r : S_r →
  S_{r+1}` and `circleK' k r : (S^{1-*})_r → (S^{1-*})_{r+1}` are the homotopies. In the
  homotopy identities the incoming term `K_{r-1}` is followed by the identity transport
  `S_{r-1+1} = S_r`.
* Labels: the cell `[w]` and its dual sit at `4w/k`, the cell `e_w` and its dual at `(4w+2)/k`
  (`circleLabel`); propagation is measured in `ℝ/4ℤ`, and `h/2 = 2/k`.
-/

open CategoryTheory
open scoped NNReal

namespace HSP.ChainModels

open FreeQ DualCat

variable (k : ℕ)

/-- The label of a cell of `S_{k,r}` (and of its dual): its center, `4w/k` or `(4w+2)/k`. -/
noncomputable def circleLabel (r : ℤ) (a : Fin ((circleComplex k).X r).dim) :
    AddCircle (4 : ℝ) :=
  ((4 * ((circleCell k r a).1 : ℕ) + if (circleCell k r a).2 then 2 else 0) / k : ℝ)

private lemma circleDim_eq_zero {r : ℤ} (h0 : r ≠ 0) (h1 : r ≠ 1) :
    ((circleComplex k).X r).dim = 0 := by
  rcases r with (_ | _ | r) | r
  · exact absurd rfl h0
  · exact absurd rfl h1
  · rfl
  · rfl

private lemma hom_eq_of_dim {X Y : FreeQ} (f g : X ⟶ Y) (h : X.dim = 0 ∨ Y.dim = 0) :
    f = g :=
  Matrix.ext fun i j => h.elim (fun h => (Fin.cast h j).elim0) (fun h => (Fin.cast h i).elim0)

private lemma comp_eq_zero_of_dim {X Y Z : FreeQ} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Y.dim = 0) :
    f ≫ g = 0 :=
  Matrix.ext fun i j => by
    change (toMatrix g * toMatrix f) i j = 0
    rw [Matrix.mul_apply]
    exact Finset.sum_eq_zero fun c _ => (Fin.cast h c).elim0

/-- The shift `[w] ↦ [w+1]` as a matrix. -/
private def Bm : Matrix (Fin k) (Fin k) ℚ :=
  Matrix.of fun a b => if (a : ℕ) = ((b : ℕ) + 1) % k then 1 else 0

/-- The shift `[w] ↦ [w-1]` as a matrix. -/
private def Pm : Matrix (Fin k) (Fin k) ℚ :=
  Matrix.of fun a b => if (a : ℕ) = ((b : ℕ) + k - 1) % k then 1 else 0

private lemma pred_mod {b : ℕ} (hb : b < k) :
    (b + k - 1) % k = if b = 0 then k - 1 else b - 1 := by
  split_ifs with h
  · subst h; rw [zero_add]; exact Nat.mod_eq_of_lt (by omega)
  · rw [show b + k - 1 = b - 1 + k by omega, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt (by omega)

private lemma succ_mod {b : ℕ} (hb : b < k) :
    (b + 1) % k = if b + 1 = k then 0 else b + 1 := by
  split_ifs with h
  · rw [h, Nat.mod_self]
  · exact Nat.mod_eq_of_lt (by omega)

private lemma sum_ind (P : Fin k → ℚ) (m : ℕ) (hm : m < k) :
    ∑ c : Fin k, P c * (if (c : ℕ) = m then 1 else 0) = P ⟨m, hm⟩ := by
  rw [Finset.sum_eq_single ⟨m, hm⟩]
  · simp
  · intro c _ hc
    have : (c : ℕ) ≠ m := fun h => hc (Fin.ext h)
    simp [this]
  · simp

private lemma Pm_mul_Bm : Pm k * Bm k = 1 := by
  refine Matrix.ext fun a b => ?_
  rw [Matrix.mul_apply]
  simp only [Pm, Bm, Matrix.of_apply]
  rw [sum_ind k _ _ (Nat.mod_lt _ (Fin.pos b))]
  simp only [Matrix.one_apply, Fin.ext_iff]
  simp only [pred_mod k (Nat.mod_lt _ (Fin.pos b))]
  simp only [succ_mod k b.2]
  have := a.2; have := b.2
  split_ifs <;> first | rfl | contradiction | omega

private lemma Bm_mul_Pm : Bm k * Pm k = 1 := by
  refine Matrix.ext fun a b => ?_
  rw [Matrix.mul_apply]
  simp only [Pm, Bm, Matrix.of_apply]
  rw [sum_ind k _ _ (Nat.mod_lt _ (Fin.pos b))]
  simp only [Matrix.one_apply, Fin.ext_iff]
  simp only [succ_mod k (Nat.mod_lt _ (Fin.pos b))]
  simp only [pred_mod k b.2]
  have := a.2; have := b.2
  split_ifs <;> first | rfl | contradiction | omega

private lemma transpose_Bm : (Bm k).transpose = Pm k := by
  refine Matrix.ext fun a b => ?_
  simp only [Matrix.transpose_apply, Pm, Bm, Matrix.of_apply]
  rw [pred_mod k b.2, succ_mod k a.2]
  have := a.2; have := b.2
  congr 1
  apply propext
  split_ifs <;> first | rfl | contradiction | omega

private lemma transpose_Pm : (Pm k).transpose = Bm k := by
  rw [← transpose_Bm, Matrix.transpose_transpose]


/-! ### Components as `k × k` matrices -/

/-- A morphism between objects of dimension `k`, read as a `k × k` matrix. -/
private def toMk {X Y : FreeQ} (f : X ⟶ Y) (hX : X = ⟨k⟩) (hY : Y = ⟨k⟩) :
    Matrix (Fin k) (Fin k) ℚ :=
  Matrix.of fun a b => toMatrix f (Fin.cast (by rw [hY]) a) (Fin.cast (by rw [hX]) b)

private lemma toMk_injective {X Y : FreeQ} {f g : X ⟶ Y} (hX : X = ⟨k⟩) (hY : Y = ⟨k⟩)
    (h : toMk k f hX hY = toMk k g hX hY) : f = g := by
  subst hX hY; exact h

private lemma toMk_comp {X Y Z : FreeQ} (hX : X = ⟨k⟩) (hY : Y = ⟨k⟩) (hZ : Z = ⟨k⟩)
    (f : X ⟶ Y) (g : Y ⟶ Z) : toMk k (f ≫ g) hX hZ = toMk k g hY hZ * toMk k f hX hY := by
  subst hX hY hZ; rfl

private lemma toMk_add {X Y : FreeQ} (hX : X = ⟨k⟩) (hY : Y = ⟨k⟩) (f g : X ⟶ Y) :
    toMk k (f + g) hX hY = toMk k f hX hY + toMk k g hX hY := by
  subst hX hY; rfl

private lemma toMk_sub {X Y : FreeQ} (hX : X = ⟨k⟩) (hY : Y = ⟨k⟩) (f g : X ⟶ Y) :
    toMk k (f - g) hX hY = toMk k f hX hY - toMk k g hX hY := by
  subst hX hY; rfl

private lemma toMk_neg {X Y : FreeQ} (hX : X = ⟨k⟩) (hY : Y = ⟨k⟩) (f : X ⟶ Y) :
    toMk k (-f) hX hY = -toMk k f hX hY := by
  subst hX hY; rfl

private lemma toMk_smul {X Y : FreeQ} (hX : X = ⟨k⟩) (hY : Y = ⟨k⟩) (c : ℚ) (f : X ⟶ Y) :
    toMk k (c • f) hX hY = c • toMk k f hX hY := by
  subst hX hY; rfl

private lemma toMk_zero {X Y : FreeQ} (hX : X = ⟨k⟩) (hY : Y = ⟨k⟩) :
    toMk k (0 : X ⟶ Y) hX hY = 0 := by
  subst hX hY; rfl

private lemma toMk_id {X : FreeQ} (hX : X = ⟨k⟩) : toMk k (𝟙 X) hX hX = 1 := by
  subst hX; rfl

private lemma toMk_dualHom {X Y : FreeQ} (hX : X = ⟨k⟩) (hY : Y = ⟨k⟩) (hX' : dual X = ⟨k⟩)
    (hY' : dual Y = ⟨k⟩) (f : X ⟶ Y) :
    toMk k (dualHom f) hY' hX' = (toMk k f hX hY).transpose := by
  subst hX hY; rfl

private lemma toMk_eqToHom {X Y : FreeQ} (hX : X = ⟨k⟩) (hY : Y = ⟨k⟩) (h : X = Y) :
    toMk k (eqToHom h) hX hY = 1 := by
  subst hX hY; rfl

private lemma M_add_apply {n : ℤ} (f g : (StructureCx (circleComplex k)).X n) (x) :
    (f + g) x = f x + g x := rfl

private lemma M_smul_apply {n : ℤ} (c : ℚ) (f : (StructureCx (circleComplex k)).X n) (x) :
    (c • f) x = c • f x := rfl

private lemma M_zero_apply {n : ℤ} (x) : (0 : (StructureCx (circleComplex k)).X n) x = 0 := rfl

private lemma ext_M {n : ℤ} (f g : (StructureCx (circleComplex k)).X n)
    (h00 : ∀ h : (0 : ℤ) + 0 = n, f ⟨(0, 0), h⟩ = g ⟨(0, 0), h⟩)
    (h01 : ∀ h : (0 : ℤ) + 1 = n, f ⟨(0, 1), h⟩ = g ⟨(0, 1), h⟩)
    (h10 : ∀ h : (1 : ℤ) + 0 = n, f ⟨(1, 0), h⟩ = g ⟨(1, 0), h⟩)
    (h11 : ∀ h : (1 : ℤ) + 1 = n, f ⟨(1, 1), h⟩ = g ⟨(1, 1), h⟩) : f = g := by
  funext ⟨⟨p, q⟩, h⟩
  by_cases hq : q = 0 ∨ q = 1
  · by_cases hp : p = 0 ∨ p = 1
    · rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
      exacts [h00 h, h01 h, h10 h, h11 h]
    · push Not at hp
      exact hom_eq_of_dim _ _ (Or.inr (circleDim_eq_zero k hp.1 hp.2))
  · push Not at hq
    exact hom_eq_of_dim _ _ (Or.inl (circleDim_eq_zero k hq.1 hq.2))


private lemma toMk_negOnePow_even {X Y : FreeQ} (hX : X = ⟨k⟩) (hY : Y = ⟨k⟩) (f : X ⟶ Y)
    {n : ℤ} (hn : n = 0) : toMk k (n.negOnePow • f) hX hY = toMk k f hX hY := by
  rw [hn, Int.negOnePow_zero, one_smul]

private lemma toMk_negOnePow_odd {X Y : FreeQ} (hX : X = ⟨k⟩) (hY : Y = ⟨k⟩) (f : X ⟶ Y)
    {n : ℤ} (hn : n = 1) : toMk k (n.negOnePow • f) hX hY = -toMk k f hX hY := by
  rw [hn, Int.negOnePow_one, Units.neg_smul, one_smul, toMk_neg]

private lemma objX (e : ℤ) (he : e = 0 ∨ e = 1) : (circleComplex k).X e = ⟨k⟩ := by
  rcases he with rfl | rfl <;> rfl

private lemma objD (e : ℤ) (he : e = 0 ∨ e = 1) : dual ((circleComplex k).X e) = ⟨k⟩ :=
  objX k e he

/-! ### The components -/

private lemma circleD10 {p q : ℤ} (hp : p = 1) (hq : q = 0) :
    toMk k ((circleComplex k).d p q) (objX k p (.inr hp)) (objX k q (.inl hq)) = Bm k - 1 := by
  subst hp hq
  rw [circleComplex_d]
  refine Matrix.ext fun a b => ?_
  simp [toMk, circleDiffMatrix, Bm, Matrix.one_apply, Fin.ext_iff]; rfl

private lemma phi01 {p q : ℤ} (hp : p = 0) (hq : q = 1) (h : p + q = 1) :
    toMk k (circlePhi k ⟨(p, q), h⟩) (objD k q (.inr hq)) (objX k p (.inl hp)) = 1 := by
  subst hp hq
  refine Matrix.ext fun a b => ?_
  simp [toMk, circlePhi, Matrix.one_apply, Fin.ext_iff]

private lemma phi10 {p q : ℤ} (hp : p = 1) (hq : q = 0) (h : p + q = 1) :
    toMk k (circlePhi k ⟨(p, q), h⟩) (objD k q (.inl hq)) (objX k p (.inr hp)) = Pm k := by
  subst hp hq
  refine Matrix.ext fun a b => ?_
  simp [toMk, circlePhi, Pm]

private lemma H11 {p q : ℤ} (hp : p = 1) (hq : q = 1) (h : p + q = 2) :
    toMk k (circleH k ⟨(p, q), h⟩) (objD k q (.inr hq)) (objX k p (.inr hp)) = 1 := by
  subst hp hq
  refine Matrix.ext fun a b => ?_
  simp [toMk, circleH, Matrix.one_apply, Fin.ext_iff]

private lemma H_ne (x : {x : ℤ × ℤ // x.1 + x.2 = 2}) (hx : x.1.1 ≠ 1) : circleH k x = 0 := by
  refine Matrix.ext fun a b => ?_
  simp [circleH, hx]

/-- Closes the side goals left by the rewriting lemmas. -/
local macro "side_goals" : tactic =>
  `(tactic| all_goals first
    | exact objD _ _ (by norm_num) | exact objX _ _ (by norm_num) | norm_num)

private lemma dH01 {p q : ℤ} (hp : p = 0) (hq : q = 1) (h : p + q = 1) :
    toMk k ((StructureCx (circleComplex k)).d 2 1 (circleH k) ⟨(p, q), h⟩)
      (objD k q (.inr hq)) (objX k p (.inl hp)) = Bm k - 1 := by
  subst hp hq
  rw [StructureCx.d_apply _ _ _ _ 0 1 h 1 2 rfl rfl,
    comp_eq_zero_of_dim _ _ (show (dual ((circleComplex k).X 2)).dim = 0 from rfl), smul_zero,
    add_zero, toMk_comp, H11, circleD10, Matrix.mul_one]
  side_goals

private lemma dH10 {p q : ℤ} (hp : p = 1) (hq : q = 0) (h : p + q = 1) :
    toMk k ((StructureCx (circleComplex k)).d 2 1 (circleH k) ⟨(p, q), h⟩)
      (objD k q (.inl hq)) (objX k p (.inr hp)) = -(Pm k - 1) := by
  subst hp hq
  rw [StructureCx.d_apply _ _ _ _ 1 0 h 2 1 rfl rfl,
    comp_eq_zero_of_dim _ _ (show ((circleComplex k).X 2).dim = 0 from rfl), zero_add,
    toMk_negOnePow_odd, toMk_comp, toMk_dualHom, circleD10, H11, Matrix.one_mul,
    Matrix.transpose_sub, transpose_Bm, Matrix.transpose_one]
  side_goals

private lemma phiSym01 {p q : ℤ} (hp : p = 0) (hq : q = 1) (h : p + q = 1) :
    toMk k (circlePhiSym k ⟨(p, q), h⟩) (objD k q (.inr hq)) (objX k p (.inl hp)) =
      1 + (1 / 2 : ℚ) • (Bm k - 1) := by
  rw [circlePhiSym, M_add_apply, M_smul_apply, toMk_add, toMk_smul, phi01 k hp hq, dH01 k hp hq]

private lemma phiSym10 {p q : ℤ} (hp : p = 1) (hq : q = 0) (h : p + q = 1) :
    toMk k (circlePhiSym k ⟨(p, q), h⟩) (objD k q (.inl hq)) (objX k p (.inr hp)) =
      Pm k + (1 / 2 : ℚ) • -(Pm k - 1) := by
  rw [circlePhiSym, M_add_apply, M_smul_apply, toMk_add, toMk_smul, phi10 k hp hq, dH10 k hp hq]

private lemma B0 {r : ℤ} (hr : r = 0) :
    toMk k (circleB k r) (objX k r (.inl hr)) (objD k (1 - r) (.inr (by omega))) = 1 := by
  subst hr
  refine Matrix.ext fun a b => ?_
  simp [toMk, circleB, Matrix.one_apply, Fin.ext_iff]

private lemma B1 {r : ℤ} (hr : r = 1) :
    toMk k (circleB k r) (objX k r (.inr hr)) (objD k (1 - r) (.inl (by omega))) = Bm k := by
  subst hr
  refine Matrix.ext fun a b => ?_
  simp [toMk, circleB, Bm]

private lemma K0 {r : ℤ} (hr : r = 0) :
    toMk k (circleK k r) (objX k r (.inl hr)) (objX k (r + 1) (.inr (by omega))) =
      (1 / 2 : ℚ) • 1 := by
  subst hr
  rw [circleK, toMk_smul, toMk_comp, H11, B0, Matrix.one_mul]
  side_goals

private lemma K'0 {r : ℤ} (hr : r = 0) :
    toMk k (circleK' k r) (objD k (1 - r) (.inr (by omega)))
      (objD k (1 - (r + 1)) (.inl (by omega))) = (1 / 2 : ℚ) • Bm k := by
  subst hr
  rw [circleK', toMk_smul, toMk_comp, H11, B1, Matrix.mul_one]
  side_goals

private lemma K_ne {r : ℤ} (hr : r ≠ 0) : circleK k r = 0 := by
  rw [circleK, H_ne k _ (by simp only; omega), Limits.comp_zero, smul_zero]

private lemma K'_ne {r : ℤ} (hr : r ≠ 0) : circleK' k r = 0 := by
  rw [circleK', H_ne k _ (by simp only; omega), Limits.zero_comp, smul_zero]


/-! ### The augmentation -/

/-- A morphism `ℚ^k → ℚ`, read as a row of length `k`. -/
private def toRow {X : FreeQ} (f : X ⟶ (⟨1⟩ : FreeQ)) (hX : X = ⟨k⟩) : Matrix (Fin 1) (Fin k) ℚ :=
  Matrix.of fun i b => toMatrix f i (Fin.cast (by rw [hX]) b)

private lemma toRow_injective {X : FreeQ} {f g : X ⟶ (⟨1⟩ : FreeQ)} (hX : X = ⟨k⟩)
    (h : toRow k f hX = toRow k g hX) : f = g := by
  subst hX; exact h

private lemma toRow_comp {X Y : FreeQ} (hX : X = ⟨k⟩) (hY : Y = ⟨k⟩) (f : X ⟶ Y)
    (g : Y ⟶ (⟨1⟩ : FreeQ)) : toRow k (f ≫ g) hX = toRow k g hY * toMk k f hX hY := by
  subst hX hY; rfl

private lemma ones_mul_Bm :
    (Matrix.of fun _ _ => (1 : ℚ) : Matrix (Fin 1) (Fin k) ℚ) * Bm k = Matrix.of fun _ _ => 1 := by
  refine Matrix.ext fun i b => ?_
  rw [Matrix.mul_apply]
  simp only [Bm, Matrix.of_apply]
  exact sum_ind k (fun _ => 1) _ (Nat.mod_lt _ (Fin.pos b))

/-! ### Propagation -/

/-- The point `(4i + s)/k` of `ℝ/4ℤ`. -/
private noncomputable def L (i : ℕ) (s : ℝ) : AddCircle (4 : ℝ) :=
  (((4 * (i : ℝ) + s) / k : ℝ) : AddCircle (4 : ℝ))

private lemma label0 {r : ℤ} (hr : r = 0) (a : Fin ((circleComplex k).X r).dim) :
    circleLabel k r a = L k a 0 := by
  subst hr; rfl

private lemma label1 {r : ℤ} (hr : r = 1) (a : Fin ((circleComplex k).X r).dim) :
    circleLabel k r a = L k a 2 := by
  subst hr; rfl

private lemma dist_L {i j : ℕ} {s s' : ℝ} (hk : 0 < k) (m : ℤ)
    (h : |4 * (i : ℝ) + s - (4 * j + s') + 4 * m * k| ≤ 2) :
    dist (L k i s) (L k j s') ≤ 2 / k := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have e : (L k i s - L k j s' : AddCircle (4 : ℝ)) =
      (((4 * (i : ℝ) + s - (4 * j + s') + 4 * m * k) / k : ℝ) : AddCircle (4 : ℝ)) := by
    unfold L
    rw [← AddCircle.coe_sub, QuotientAddGroup.eq_iff_sub_mem]
    refine AddSubgroup.mem_zmultiples_iff.2 ⟨-m, ?_⟩
    rw [zsmul_eq_mul]
    field_simp
    push_cast
    ring
  rw [dist_eq_norm, e]
  refine QuotientAddGroup.norm_mk_le_norm.trans ?_
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hk']
  exact div_le_div_of_nonneg_right h hk'.le

private lemma d_eq {i : ℕ} {s s' : ℝ} (hk : 0 < k) (h : |s - s'| ≤ 2) :
    dist (L k i s) (L k i s') ≤ 2 / k :=
  dist_L k hk 0 (by convert h using 2; push_cast; ring)

private lemma d_succ {i j : ℕ} (hj : j < k) (h : i = (j + 1) % k) :
    dist (L k i 0) (L k j 2) ≤ 2 / k := by
  rw [succ_mod k hj] at h
  split_ifs at h with hj1
  · subst h
    refine dist_L k (by omega) 1 ?_
    have : (j : ℝ) + 1 = k := by exact_mod_cast hj1
    rw [abs_le]; constructor <;> push_cast <;> nlinarith
  · subst h
    refine dist_L k (by omega) 0 ?_
    rw [abs_le]; constructor <;> push_cast <;> linarith

private lemma d_pred {i j : ℕ} (hj : j < k) (h : i = (j + k - 1) % k) :
    dist (L k i 2) (L k j 0) ≤ 2 / k := by
  rw [pred_mod k hj] at h
  split_ifs at h with hj0
  · subst h hj0
    refine dist_L k (by omega) (-1) ?_
    have : ((k - 1 : ℕ) : ℝ) + 1 = k := by exact_mod_cast (by omega : k - 1 + 1 = k)
    rw [abs_le]; constructor <;> push_cast <;> nlinarith
  · subst h
    refine dist_L k (by omega) 0 ?_
    have : ((j - 1 : ℕ) : ℝ) + 1 = j := by exact_mod_cast (by omega : j - 1 + 1 = j)
    rw [abs_le]; constructor <;> push_cast <;> linarith

private lemma prop_le {B B' : Type*} [Fintype B] [Fintype B'] (l : B → AddCircle (4 : ℝ))
    (l' : B' → AddCircle (4 : ℝ)) (u : Matrix B' B ℚ)
    (h : ∀ i j, u i j ≠ 0 → dist (l' i) (l j) ≤ 2 / k) : (prop l l' u : ℝ) ≤ 2 / k := by
  have h2 : (0 : ℝ) ≤ 2 / k := by positivity
  have : prop l l' u ≤ (⟨2 / k, h2⟩ : ℝ≥0) := by
    refine Finset.sup_le fun q hq => ?_
    rw [Finset.mem_filter] at hq
    exact NNReal.coe_le_coe.1 (by rw [coe_nndist]; exact h _ _ hq.2)
  exact (NNReal.coe_le_coe.2 this).trans_eq rfl

private lemma ent01 (a b : Fin k) (h : (1 + (1 / 2 : ℚ) • (Bm k - 1)) a b ≠ 0) :
    (a : ℕ) = b ∨ (a : ℕ) = ((b : ℕ) + 1) % k := by
  by_contra hc
  push Not at hc
  apply h
  simp [Bm, Fin.ext_iff, hc.1, hc.2]

private lemma ent10 (a b : Fin k) (h : (Pm k + (1 / 2 : ℚ) • -(Pm k - 1)) a b ≠ 0) :
    (a : ℕ) = b ∨ (a : ℕ) = ((b : ℕ) + k - 1) % k := by
  by_contra hc
  push Not at hc
  apply h
  simp [Pm, Fin.ext_iff, hc.1, hc.2]

private lemma ent_one (a b : Fin k) (h : ((1 / 2 : ℚ) • (1 : Matrix (Fin k) (Fin k) ℚ)) a b ≠ 0) :
    (a : ℕ) = b := by
  by_contra hc
  apply h
  simp [Fin.ext_iff, hc]

private lemma ent_Bm (a b : Fin k) (h : ((1 / 2 : ℚ) • Bm k) a b ≠ 0) :
    (a : ℕ) = ((b : ℕ) + 1) % k := by
  by_contra hc
  apply h
  simp [Bm, hc]

/-! ### The proof -/

private lemma circle_d_phi : (StructureCx (circleComplex k)).d 1 0 (circlePhi k) = 0 := by
  refine ext_M k _ _ (fun h => ?_) (fun h => by norm_num at h) (fun h => by norm_num at h)
    (fun h => by norm_num at h)
  rw [StructureCx.d_apply _ _ _ _ 0 0 h 1 1 rfl rfl, M_zero_apply]
  refine toMk_injective k (objD k 0 (by norm_num)) (objX k 0 (by norm_num)) ?_
  rw [toMk_add, toMk_negOnePow_even, toMk_comp, toMk_comp, toMk_dualHom, circleD10, phi10,
    phi01, toMk_zero, Matrix.transpose_sub, transpose_Bm, Matrix.transpose_one, Matrix.one_mul,
    Matrix.sub_mul, Bm_mul_Pm, Matrix.one_mul]
  · abel
  side_goals

private lemma circle_T_phi : (StructureCx.T (circleComplex k)).f 1 (circlePhi k) =
    circlePhi k + (StructureCx (circleComplex k)).d 2 1 (circleH k) := by
  refine ext_M k _ _ (fun h => by norm_num at h) (fun h => ?_) (fun h => ?_)
    (fun h => by norm_num at h)
  · rw [StructureCx.T_apply, M_add_apply]
    refine toMk_injective k (objD k 1 (by norm_num)) (objX k 0 (by norm_num)) ?_
    rw [toMk_negOnePow_even, toMk_comp, toMk_eqToHom, toMk_dualHom, phi10, toMk_add, phi01, dH01,
      transpose_Pm, Matrix.one_mul]
    · abel
    side_goals
  · rw [StructureCx.T_apply, M_add_apply]
    refine toMk_injective k (objD k 0 (by norm_num)) (objX k 1 (by norm_num)) ?_
    rw [toMk_negOnePow_even, toMk_comp, toMk_eqToHom, toMk_dualHom, phi01, toMk_add, phi10, dH10,
      Matrix.transpose_one, Matrix.one_mul]
    · abel
    side_goals

/-- **Circle duality.** For the circle complex `S = S_k`:
1. `∂φ = 0`, and `φ_♮ : S^{1-*} → S` is an isomorphism with inverse `b`;
2. `Tφ = φ + ∂H`, so `φ^s = ½(φ + Tφ)`, `∂φ^s = 0` and `Tφ^s = φ^s`;
3. `φ^s b - 1 = dK + Kd` and `b φ^s - 1 = dK' + K'd`;
4. `ε φ^s(e_w^*) = 1 = e_w^*(∑_v e_v)`;
5. with cells and duals labelled at the centers, `φ`, `φ^s`, `b`, `H`, `K`, `K'` have propagation
   at most `h/2 = 2/k`. -/
theorem circle_duality :
    -- (1)
    ((StructureCx (circleComplex k)).d 1 0 (circlePhi k) = 0 ∧
      ∀ r : ℤ, circlePhi k ⟨(r, 1 - r), by ring⟩ ≫ circleB k r = 𝟙 _ ∧
        circleB k r ≫ circlePhi k ⟨(r, 1 - r), by ring⟩ = 𝟙 _) ∧
    -- (2)
    ((StructureCx.T (circleComplex k)).f 1 (circlePhi k) =
        circlePhi k + (StructureCx (circleComplex k)).d 2 1 (circleH k) ∧
      circlePhiSym k = (1 / 2 : ℚ) • (circlePhi k + (StructureCx.T (circleComplex k)).f 1
        (circlePhi k)) ∧
      (StructureCx (circleComplex k)).d 1 0 (circlePhiSym k) = 0 ∧
      (StructureCx.T (circleComplex k)).f 1 (circlePhiSym k) = circlePhiSym k) ∧
    -- (3)
    (∀ r : ℤ, circleB k r ≫ circlePhiSym k ⟨(r, 1 - r), by ring⟩ - 𝟙 _ =
        circleK k r ≫ (circleComplex k).d (r + 1) r +
          (circleComplex k).d r (r - 1) ≫ circleK k (r - 1) ≫
            eqToHom (congrArg (circleComplex k).X (by ring))) ∧
    (∀ r : ℤ, circlePhiSym k ⟨(r, 1 - r), by ring⟩ ≫ circleB k r - 𝟙 _ =
        circleK' k r ≫ (dualCx (circleComplex k) 1).d (r + 1) r +
          (dualCx (circleComplex k) 1).d r (r - 1) ≫ circleK' k (r - 1) ≫
            eqToHom (congrArg (dualCx (circleComplex k) 1).X (by ring))) ∧
    -- (4)
    (circlePhiSym k ⟨(0, 1), by ring⟩ ≫ circleAug k = ofMatrix (Matrix.of fun _ _ => 1) ∧
      dualHom (circleFundamental k) = ofMatrix (Matrix.of fun _ _ => 1)) ∧
    -- (5)
    ((∀ x, (prop (circleLabel k x.1.2) (circleLabel k x.1.1) (circlePhi k x) : ℝ) ≤ 2 / k) ∧
      (∀ x, (prop (circleLabel k x.1.2) (circleLabel k x.1.1) (circlePhiSym k x) : ℝ) ≤ 2 / k) ∧
      (∀ x, (prop (circleLabel k x.1.2) (circleLabel k x.1.1) (circleH k x) : ℝ) ≤ 2 / k) ∧
      (∀ r, (prop (circleLabel k r) (circleLabel k (1 - r)) (circleB k r) : ℝ) ≤ 2 / k) ∧
      (∀ r, (prop (circleLabel k r) (circleLabel k (r + 1)) (circleK k r) : ℝ) ≤ 2 / k) ∧
      (∀ r, (prop (circleLabel k (1 - r)) (circleLabel k (1 - (r + 1))) (circleK' k r) : ℝ) ≤
        2 / k)) := by
  have h1a := circle_d_phi k
  have h2a := circle_T_phi k
  have h2b : circlePhiSym k = (1 / 2 : ℚ) • (circlePhi k + (StructureCx.T (circleComplex k)).f 1
      (circlePhi k)) := by
    rw [h2a, circlePhiSym]; module
  have hT : (StructureCx (circleComplex k)).d 1 0 ((StructureCx.T (circleComplex k)).f 1
      (circlePhi k)) = (StructureCx.T (circleComplex k)).f 0
        ((StructureCx (circleComplex k)).d 1 0 (circlePhi k)) := by
    have := congrArg (fun g => g.hom (circlePhi k)) ((StructureCx.T (circleComplex k)).comm 1 0)
    simpa using this
  have hTT : (StructureCx.T (circleComplex k)).f 1 ((StructureCx.T (circleComplex k)).f 1
      (circlePhi k)) = circlePhi k := by
    have := congrArg (fun g => (g.f 1).hom (circlePhi k)) (StructureCx.T_sq (circleComplex k))
    simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f, ModuleCat.hom_comp,
      ModuleCat.hom_id, LinearMap.comp_apply, LinearMap.id_apply] at this
    exact this
  refine ⟨⟨h1a, fun r => ?_⟩, ⟨h2a, h2b, ?_, ?_⟩, fun r => ?_, fun r => ?_, ⟨?_, ?_⟩,
    ⟨?_, ?_, ?_, fun r => ?_, fun r => ?_, fun r => ?_⟩⟩
  -- (1) `b` inverts `φ`
  · rcases (show r = 0 ∨ r = 1 ∨ (r ≠ 0 ∧ r ≠ 1) by omega) with rfl | rfl | ⟨h0, h1⟩
    · constructor
      · refine toMk_injective k (objD k (1 - 0) (by norm_num)) (objD k (1 - 0) (by norm_num)) ?_
        rw [toMk_comp, toMk_id, phi01, B0, Matrix.mul_one]
        side_goals
      · refine toMk_injective k (objX k 0 (by norm_num)) (objX k 0 (by norm_num)) ?_
        rw [toMk_comp, toMk_id, phi01, B0, Matrix.mul_one]
        side_goals
    · constructor
      · refine toMk_injective k (objD k (1 - 1) (by norm_num)) (objD k (1 - 1) (by norm_num)) ?_
        rw [toMk_comp, toMk_id, phi10, B1, Bm_mul_Pm]
        side_goals
      · refine toMk_injective k (objX k 1 (by norm_num)) (objX k 1 (by norm_num)) ?_
        rw [toMk_comp, toMk_id, phi10, B1, Pm_mul_Bm]
        side_goals
    · exact ⟨hom_eq_of_dim _ _ (Or.inl (circleDim_eq_zero k (r := 1 - r) (by omega) (by omega))),
        hom_eq_of_dim _ _ (Or.inl (circleDim_eq_zero k h0 h1))⟩
  -- (2) `∂φ^s = 0`
  · rw [h2b, map_smul, map_add, hT, h1a, map_zero, add_zero, smul_zero]
  -- (2) `Tφ^s = φ^s`
  · rw [h2b, map_smul, map_add, hTT, add_comm]
  -- (3) `φ^s b - 1 = dK + Kd`
  · rcases (show r = 0 ∨ r = 1 ∨ (r ≠ 0 ∧ r ≠ 1) by omega) with rfl | rfl | ⟨h0, h1⟩
    · simp only [comp_eq_zero_of_dim ((circleComplex k).d 0 (0 - 1)) _
        (circleDim_eq_zero k (r := 0 - 1) (by norm_num) (by norm_num)), add_zero]
      refine toMk_injective k (objX k 0 (by norm_num)) (objX k 0 (by norm_num)) ?_
      rw [toMk_sub, toMk_comp, toMk_comp, toMk_id, phiSym01, B0, circleD10, K0]
      · simp only [Matrix.mul_one, Matrix.mul_smul]
        module
      side_goals
    · rw [comp_eq_zero_of_dim (circleK k 1) ((circleComplex k).d (1 + 1) 1)
        (circleDim_eq_zero k (by norm_num) (by norm_num)), zero_add]
      refine toMk_injective k (objX k 1 (by norm_num)) (objX k 1 (by norm_num)) ?_
      rw [toMk_sub, toMk_comp, toMk_comp, toMk_comp, toMk_id, toMk_eqToHom, phiSym10, B1,
        circleD10, K0]
      · simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.neg_mul, Matrix.sub_mul, Pm_mul_Bm,
          Matrix.one_mul]
        module
      side_goals
    · exact hom_eq_of_dim _ _ (Or.inl (circleDim_eq_zero k h0 h1))
  -- (3) `b φ^s - 1 = dK' + K'd`
  · rcases (show r = 0 ∨ r = 1 ∨ (r ≠ 0 ∧ r ≠ 1) by omega) with rfl | rfl | ⟨h0, h1⟩
    · simp only [comp_eq_zero_of_dim ((dualCx (circleComplex k) 1).d 0 (0 - 1)) _
        (circleDim_eq_zero k (r := 1 - (0 - 1)) (by norm_num) (by norm_num)), add_zero]
      refine toMk_injective k (objD k (1 - 0) (by norm_num)) (objD k (1 - 0) (by norm_num)) ?_
      rw [toMk_sub, toMk_comp, toMk_comp, toMk_id, phiSym01, B0, toMk_negOnePow_odd,
        toMk_dualHom, circleD10, K'0, Matrix.transpose_sub, transpose_Bm, Matrix.transpose_one]
      · simp only [Matrix.one_mul, Matrix.neg_mul, Matrix.sub_mul, Matrix.mul_smul, Pm_mul_Bm]
        module
      side_goals
    · rw [comp_eq_zero_of_dim (circleK' k 1) ((dualCx (circleComplex k) 1).d (1 + 1) 1)
        (circleDim_eq_zero k (r := 1 - (1 + 1)) (by norm_num) (by norm_num)), zero_add]
      refine toMk_injective k (objD k (1 - 1) (by norm_num)) (objD k (1 - 1) (by norm_num)) ?_
      rw [toMk_sub, toMk_comp, toMk_comp, toMk_comp, toMk_id, toMk_eqToHom, phiSym10, B1,
        toMk_negOnePow_odd, toMk_dualHom, circleD10, K'0, Matrix.transpose_sub,
        transpose_Bm, Matrix.transpose_one]
      · simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_neg, Matrix.mul_sub, Bm_mul_Pm,
          Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul]
        module
      side_goals
    · exact hom_eq_of_dim _ _ (Or.inl (circleDim_eq_zero k (r := 1 - r) (by omega) (by omega)))
  -- (4) `ε φ^s(e_w^*) = 1`
  · refine toRow_injective k (objD k 1 (by norm_num)) ?_
    rw [toRow_comp k (objD k 1 (by norm_num)) (objX k 0 (by norm_num)), phiSym01]
    · have hA : toRow k (circleAug k) (objX k 0 (by norm_num)) = Matrix.of fun _ _ => 1 := rfl
      rw [hA, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, Matrix.mul_sub, Matrix.mul_one,
        ones_mul_Bm, sub_self, smul_zero, add_zero]
      rfl
    side_goals
  · exact Matrix.ext fun _ _ => rfl
  -- (5) `φ`
  · rintro ⟨⟨p, q⟩, h⟩
    refine prop_le k _ _ _ fun a b hab => ?_
    simp only [circlePhi, Matrix.of_apply] at hab
    split_ifs at hab with hp0 hab' hp1 hab'' <;> try exact absurd rfl hab
    · obtain rfl : q = 1 := by omega
      subst hp0
      rw [label0 k rfl, label1 k rfl, hab']
      exact d_eq k (lt_of_le_of_lt (Nat.zero_le _) b.2) (by norm_num)
    · obtain rfl : q = 0 := by omega
      subst hp1
      rw [label1 k rfl, label0 k rfl]
      exact d_pred k b.2 hab''
  -- (5) `φ^s`
  · rintro ⟨⟨p, q⟩, h⟩
    refine prop_le k _ _ _ fun a b hab => ?_
    simp only at a b hab ⊢
    by_cases hp : p = 0 ∨ p = 1
    · rcases hp with rfl | rfl
      · obtain rfl : q = 1 := by omega
        have e := phiSym01 k rfl rfl h
        have hab2 : (1 + (1 / 2 : ℚ) • (Bm k - 1)) a b ≠ 0 := by rw [← e]; exact hab
        rw [label0 k rfl, label1 k rfl]
        rcases ent01 k a b hab2 with he | he
        · rw [he]; exact d_eq k (lt_of_le_of_lt (Nat.zero_le _) b.2) (by norm_num)
        · exact d_succ k b.2 he
      · obtain rfl : q = 0 := by omega
        have e := phiSym10 k rfl rfl h
        have hab2 : (Pm k + (1 / 2 : ℚ) • -(Pm k - 1)) a b ≠ 0 := by rw [← e]; exact hab
        rw [label1 k rfl, label0 k rfl]
        rcases ent10 k a b hab2 with he | he
        · rw [he]; exact d_eq k (lt_of_le_of_lt (Nat.zero_le _) b.2) (by norm_num)
        · exact d_pred k b.2 he
    · push Not at hp
      exact (Fin.cast (circleDim_eq_zero k hp.1 hp.2) a).elim0
  -- (5) `H`
  · rintro ⟨⟨p, q⟩, h⟩
    refine prop_le k _ _ _ fun a b hab => ?_
    simp only [circleH, Matrix.of_apply] at hab
    split_ifs at hab with hp hab' <;> try exact absurd rfl hab
    subst hp
    obtain rfl : q = 1 := by omega
    rw [label1 k rfl, label1 k rfl, hab']
    exact d_eq k (lt_of_le_of_lt (Nat.zero_le _) b.2) (by norm_num)
  -- (5) `b`
  · refine prop_le k _ _ _ fun a b hab => ?_
    simp only [circleB, Matrix.of_apply] at hab
    split_ifs at hab with hr1 hab' hr0 hab'' <;> try exact absurd rfl hab
    · subst hr1
      rw [label0 k (by norm_num), label1 k rfl]
      exact d_succ k b.2 hab'
    · subst hr0
      rw [label1 k (by norm_num), label0 k rfl, hab'']
      exact d_eq k (lt_of_le_of_lt (Nat.zero_le _) b.2) (by norm_num)
  -- (5) `K`
  · by_cases hr : r = 0
    · subst hr
      refine prop_le k _ _ _ fun a b hab => ?_
      have hab2 : ((1 / 2 : ℚ) • (1 : Matrix (Fin k) (Fin k) ℚ)) a b ≠ 0 := by
        rw [← K0 k rfl]; exact hab
      rw [label1 k (by norm_num), label0 k rfl, ent_one k a b hab2]
      exact d_eq k (lt_of_le_of_lt (Nat.zero_le _) b.2) (by norm_num)
    · rw [K_ne k hr, prop_zero, NNReal.coe_zero]; positivity
  -- (5) `K'`
  · by_cases hr : r = 0
    · subst hr
      refine prop_le k _ _ _ fun a b hab => ?_
      have hab2 : ((1 / 2 : ℚ) • Bm k) a b ≠ 0 := by
        rw [← K'0 k rfl]; exact hab
      rw [label0 k (by norm_num), label1 k (by norm_num)]
      exact d_succ k b.2 (ent_Bm k a b hab2)
    · rw [K'_ne k hr, prop_zero, NNReal.coe_zero]; positivity


end HSP.ChainModels
