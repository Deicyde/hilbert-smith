import HilbertSmithPaper.Categories.Supports.SupportSubcategory
import HilbertSmithPaper.LTheory.Base.Categories.FiltrationQuotient

/-!
# Support ideal

Let the `C_p`-action on `X` be isometric and `S ⊆ X` invariant. A morphism `[u] : M → N` of
`𝒜_𝐆(X)` factors through an object of `𝒜_S` (`FiltQuot.ideal (supp S)`) if and only if for every
`ε > 0`, eventually both endpoint labels of every nonzero entry of `u_i` lie in the open
`ε`-thickening of `S` (`HSP.factorsThrough_supp_iff`).

Restriction to a sub-basis (public companions, used by the support filtration). For a predicate
`P i k` on the indices of `M = (n_i, x_i)`, `M.restrict P` keeps the indices `k` with `P i k`
(enumerated in increasing order, `HSP.AsymPre.restrictEmb`). The coordinate inclusion
`restrictInc` and projection `restrictPro = restrictIncᵀ` have propagation `0`; they satisfy
`restrictInc ≫ restrictPro = 1` and `restrictPro ≫ restrictInc = trunc P`, the diagonal
coordinate projection onto the `k` with `P i k`. Decidability of `P` is classical.
-/

open CategoryTheory CategoryTheory.Limits Filter Topology Metric
open scoped NNReal

namespace HSP

variable {p : ℕ} {G : GroupSeq p} {X : Type*} [MetricSpace X] [AddAction (ZMod p) X]

namespace AsymPre

/-- A matrix all of whose nonzero entries join equal labels has propagation `0`. -/
private theorem prop_eq_zero_of' {B B' : Type*} [Fintype B] [Fintype B'] (l : B → X)
    (l' : B' → X) (u : Matrix B' B ℚ) (h : ∀ b' b, u b' b ≠ 0 → l' b' = l b) :
    prop l l' u = 0 :=
  le_antisymm (Finset.sup_le fun q hq => by
    rw [h q.1 q.2 (Finset.mem_filter.1 hq).2, nndist_self]) zero_le

/-- An entry bound for the propagation: a nonzero entry joins labels at distance `≤ prop`. -/
theorem nndist_le_prop {B B' : Type*} [Fintype B] [Fintype B'] (l : B → X) (l' : B' → X)
    (u : Matrix B' B ℚ) {b' : B'} {b : B} (h : u b' b ≠ 0) : nndist (l' b') (l b) ≤ prop l l' u :=
  Finset.le_sup (s := Finset.univ.filter fun q : B' × B => u q.1 q.2 ≠ 0) (b := (b', b)) (f := fun q : B' × B => nndist (l' q.1) (l q.2))
    (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)

variable (M : AsymPre G X) (P : ∀ i, Fin (M.n i) → Prop)

open scoped Classical in
/-- The number of indices `k` with `P i k`. -/
noncomputable def restrictRank (i : ℕ) : ℕ := (Finset.univ.filter (P i)).card

open scoped Classical in
/-- The increasing enumeration of the indices `k` with `P i k`. -/
noncomputable def restrictEmb (i : ℕ) : Fin (M.restrictRank P i) ↪o Fin (M.n i) :=
  (Finset.univ.filter (P i)).orderEmbOfFin rfl

variable {M P}

omit [MetricSpace X] [AddAction (ZMod p) X] in
open scoped Classical in
theorem restrictEmb_mem {i : ℕ} (k : Fin (M.restrictRank P i)) : P i (M.restrictEmb P i k) :=
  (Finset.mem_filter.1 (Finset.orderEmbOfFin_mem (Finset.univ.filter (P i)) rfl k)).2

omit [MetricSpace X] [AddAction (ZMod p) X] in
open scoped Classical in
theorem exists_restrictEmb_eq {i : ℕ} {j : Fin (M.n i)} (h : P i j) :
    ∃ k, M.restrictEmb P i k = j := by
  have hj : j ∈ Set.range ((Finset.univ.filter (P i)).orderEmbOfFin rfl) := by
    rw [Finset.range_orderEmbOfFin]; simpa using h
  exact hj

variable (M P)

/-- The restriction `M_P`: the indices `k` with `P i k`, with their labels. -/
noncomputable def restrict : AsymPre G X where
  n := M.restrictRank P
  x i k := M.x i (M.restrictEmb P i k)

omit [MetricSpace X] [AddAction (ZMod p) X] in
@[simp] theorem restrict_x (i : ℕ) (k : Fin (M.restrictRank P i)) :
    (M.restrict P).x i k = M.x i (M.restrictEmb P i k) := rfl

private theorem inclMat_ne_zero' {H : Type} [DecidableEq H] {m m' : ℕ} {e : Fin m → Fin m'}
    {a : H × Fin m'} {b : H × Fin m} (h : FreeCat.inclMat e a b ≠ 0) : a = (b.1, e b.2) := by
  by_contra h'
  exact h (by simp [FreeCat.inclMat, h'])

/-- The coordinate inclusion `M_P → M` (propagation `0`). -/
noncomputable def restrictInc : M.restrict P ⟶ M :=
  homMk (fun i => (FreeCat.ofMat (FreeCat.inclMat (M.restrictEmb P i))
      (FreeCat.inclMat_mem _) : (M.restrict P).free i ⟶ M.free i)) (by
    refine (tendsto_congr fun i => ?_).2 tendsto_const_nhds
    refine prop_eq_zero_of' _ _ _ fun a b h => ?_
    rw [inclMat_ne_zero' h]
    rfl)

/-- The coordinate projection `M → M_P`, the transpose of the inclusion. -/
noncomputable def restrictPro : M ⟶ M.restrict P := transpose (M.restrictInc P)

private theorem diag_mem {H : Type} [AddGroup H] [DecidableEq H] {m : ℕ} (d : Fin m → ℚ) :
    Matrix.diagonal (fun b : H × Fin m => d b.2) ∈ FreeCat.equivariant H m m := by
  intro g h h' k' k
  simp only [Matrix.diagonal_apply, Prod.mk.injEq, add_right_inj]

/-- The diagonal coordinate projection of `M` onto the indices `k` with `P i k`. -/
noncomputable def trunc [∀ i, DecidablePred (P i)] : M ⟶ M :=
  homMk (fun i => (FreeCat.ofMat
      (Matrix.diagonal fun b : G.G i × Fin (M.n i) => if P i b.2 then 1 else 0)
      (by exact diag_mem (H := G.G i) fun k => if P i k then 1 else 0) :
      M.free i ⟶ M.free i)) (by
    refine (tendsto_congr fun i => ?_).2 tendsto_const_nhds
    refine prop_eq_zero_of' _ _ _ fun a b h => ?_
    by_contra h'
    exact h (Matrix.diagonal_apply_ne _ fun e => h' (by rw [e])))

/-! Matrix identities over a basis `H × Fin m`, applied below by definitional unfolding. -/

private theorem inclMat_apply_emb {H : Type} [DecidableEq H] {m m' : ℕ} {e : Fin m → Fin m'}
    (he : Function.Injective e) (g : H) (k : Fin m) (b : H × Fin m) :
    FreeCat.inclMat e (g, e k) b = if b = (g, k) then 1 else 0 := by
  obtain ⟨g', k'⟩ := b
  simp only [FreeCat.inclMat, Prod.mk.injEq, he.eq_iff]
  by_cases h1 : g = g' <;> by_cases h2 : k = k' <;> simp [h1, h2, eq_comm]

private theorem inclT_mul_incl {H : Type} [DecidableEq H] [Fintype H] {m m' : ℕ}
    {e : Fin m → Fin m'} (he : Function.Injective e) :
    (FreeCat.inclMat (G := H) e).transpose * FreeCat.inclMat (G := H) e = 1 := by
  ext ⟨g, k⟩ ⟨g', k'⟩
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Matrix.transpose_apply, FreeCat.inclMat, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq' Finset.univ]
  simp only [Finset.mem_univ, ↓reduceIte, Prod.mk.injEq, he.eq_iff]

private theorem incl_mul_inclT {H : Type} [DecidableEq H] [Fintype H] {m m' : ℕ}
    {e : Fin m → Fin m'} (he : Function.Injective e) (Q : Fin m' → Prop) [DecidablePred Q]
    (hQ : ∀ j, Q j ↔ ∃ k, e k = j) :
    FreeCat.inclMat (G := H) e * (FreeCat.inclMat (G := H) e).transpose =
      Matrix.diagonal fun b => if Q b.2 then 1 else 0 := by
  ext ⟨g, j⟩ a'
  rw [Matrix.mul_apply, Matrix.diagonal_apply]
  simp only [Matrix.transpose_apply]
  by_cases hj : Q j
  · obtain ⟨k, rfl⟩ := (hQ j).1 hj
    simp only [inclMat_apply_emb he, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq' Finset.univ]
    simp only [Finset.mem_univ, ↓reduceIte, FreeCat.inclMat, hj]
    by_cases h : a' = (g, e k)
    · simp [h]
    · simp only [h, ↓reduceIte]
      exact (ite_eq_right_iff.2 fun e => absurd e.symm h).symm
  · rw [Finset.sum_eq_zero fun b _ => ?_]
    · simp [hj]
    · have : FreeCat.inclMat (G := H) e (g, j) b = 0 := by
        simp only [FreeCat.inclMat, Prod.mk.injEq]
        exact ite_eq_right_iff.2 fun h => absurd ((hQ j).2 ⟨b.2, h.2.symm⟩) hj
      rw [this, zero_mul]

private theorem diag_not {H : Type} [DecidableEq H] {m : ℕ} (Q : Fin m → Prop)
    [DecidablePred Q] :
    (Matrix.diagonal fun b : H × Fin m => if ¬Q b.2 then (1 : ℚ) else 0) =
      1 - Matrix.diagonal fun b : H × Fin m => if Q b.2 then (1 : ℚ) else 0 := by
  rw [← Matrix.diagonal_one, Matrix.diagonal_sub]
  congr 1
  funext b
  by_cases h : Q b.2 <;> simp [h]

private theorem diag_mul_diag {H : Type} [DecidableEq H] [Fintype H] {m : ℕ}
    (Q Q' : Fin m → Prop) [DecidablePred Q] [DecidablePred Q'] :
    ((Matrix.diagonal fun b : H × Fin m => if Q' b.2 then (1 : ℚ) else 0) *
      Matrix.diagonal fun b : H × Fin m => if Q b.2 then (1 : ℚ) else 0) =
      Matrix.diagonal fun b : H × Fin m => if Q b.2 ∧ Q' b.2 then (1 : ℚ) else 0 := by
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext b
  by_cases h : Q b.2 <;> by_cases h' : Q' b.2 <;> simp [h, h']

private theorem mul_diag_eq {H : Type} [DecidableEq H] [Fintype H] {m : ℕ} {B : Type*}
    (Q : Fin m → Prop) [DecidablePred Q] (u : Matrix B (H × Fin m) ℚ)
    (h : ∀ a b, u a b ≠ 0 → Q b.2) :
    (u * Matrix.diagonal fun b : H × Fin m => if Q b.2 then (1 : ℚ) else 0) = u := by
  ext a b
  rw [Matrix.mul_diagonal]
  by_cases hb : Q b.2
  · simp [hb]
  · have : u a b = 0 := by
      by_contra h'
      exact hb (h a b h')
    simp [hb, this]

private theorem diag_mul_eq {H : Type} [DecidableEq H] [Fintype H] {m : ℕ} {B : Type*}
    (Q : Fin m → Prop) [DecidablePred Q] (u : Matrix (H × Fin m) B ℚ)
    (h : ∀ a b, u a b ≠ 0 → Q a.2) :
    ((Matrix.diagonal fun b : H × Fin m => if Q b.2 then (1 : ℚ) else 0) * u) = u := by
  ext a b
  rw [Matrix.diagonal_mul]
  by_cases ha : Q a.2
  · simp [ha]
  · have : u a b = 0 := by
      by_contra h'
      exact ha (h a b h')
    simp [ha, this]

theorem restrictInc_restrictPro : M.restrictInc P ≫ M.restrictPro P = 𝟙 _ :=
  hom_ext fun i => FreeCat.hom_ext (by exact inclT_mul_incl (H := G.G i) (M.restrictEmb P i).injective)

variable [∀ i, DecidablePred (P i)]

theorem restrictPro_restrictInc : M.restrictPro P ≫ M.restrictInc P = M.trunc P := by
  refine hom_ext fun i => FreeCat.hom_ext ?_
  have hQ : ∀ j, P i j ↔ ∃ k, M.restrictEmb P i k = j :=
    fun _ => ⟨exists_restrictEmb_eq, by rintro ⟨k, rfl⟩; exact restrictEmb_mem k⟩
  exact incl_mul_inclT (H := G.G i) (M.restrictEmb P i).injective (P i) hQ

theorem trunc_not : M.trunc (fun i k => ¬P i k) = 𝟙 M - M.trunc P :=
  hom_ext fun i => FreeCat.hom_ext (by exact diag_not (H := G.G i) (P i))

theorem trunc_comp_trunc (Q : ∀ i, Fin (M.n i) → Prop) [∀ i, DecidablePred (Q i)] :
    M.trunc P ≫ M.trunc Q = M.trunc (fun i k => P i k ∧ Q i k) :=
  hom_ext fun i => FreeCat.hom_ext (by exact diag_mul_diag (H := G.G i) (P i) (Q i))

theorem trunc_congr {Q : ∀ i, Fin (M.n i) → Prop} [∀ i, DecidablePred (Q i)]
    (h : ∀ i k, P i k ↔ Q i k) : M.trunc P = M.trunc Q := by
  have : P = Q := funext fun i => funext fun k => propext (h i k)
  subst this
  congr

theorem transpose_trunc : transpose (M.trunc P) = M.trunc P :=
  hom_ext fun _ => FreeCat.hom_ext (by exact Matrix.diagonal_transpose _)

/-- If every column of `u_i` outside `P` vanishes, then `u` factors through the truncation. -/
theorem trunc_comp_eq {N : AsymPre G X} (u : M ⟶ N)
    (h : ∀ i a (b : G.G i × Fin (M.n i)), FreeCat.mat (coord u i) a b ≠ 0 → P i b.2) :
    M.trunc P ≫ u = u :=
  hom_ext fun i => FreeCat.hom_ext (by exact mul_diag_eq (H := G.G i) (P i) (FreeCat.mat (coord u i)) (h i))

/-- If eventually every row of `u_i` outside `P` vanishes, then `[u]` factors through the
truncation. -/
theorem mkHom_comp_trunc_eq {N : AsymPre G X} (u : N ⟶ M)
    (h : ∀ᶠ i in atTop, ∀ (a : G.G i × Fin (M.n i)) b, FreeCat.mat (coord u i) a b ≠ 0 →
      P i a.2) :
    AsymCat.mkHom u ≫ AsymCat.mkHom (M.trunc P) = AsymCat.mkHom u := by
  rw [← Functor.map_comp, AsymCat.mkHom_eq_iff]
  filter_upwards [h] with i hi
  exact FreeCat.hom_ext (by exact diag_mul_eq (H := G.G i) (P i) (FreeCat.mat (coord u i)) hi)

end AsymPre

variable [IsIsometricVAdd (ZMod p) X] {S : Set X}

/-- For an invariant `S` and an isometric action, `c +ᵥ y` is in the `ε`-thickening of `S` as soon
as `y` is. -/
theorem vadd_mem_thickening (hS : ∀ c : ZMod p, ∀ x ∈ S, c +ᵥ x ∈ S) (c : ZMod p) {ε : ℝ} {y : X}
    (hy : y ∈ thickening ε S) : c +ᵥ y ∈ thickening ε S := by
  obtain ⟨z, hz, hd⟩ := mem_thickening_iff.1 hy
  exact mem_thickening_iff.2 ⟨c +ᵥ z, hS c z hz, by rwa [dist_vadd]⟩

theorem vadd_mem_thickening_iff (hS : ∀ c : ZMod p, ∀ x ∈ S, c +ᵥ x ∈ S) (c : ZMod p) {ε : ℝ}
    {y : X} : c +ᵥ y ∈ thickening ε S ↔ y ∈ thickening ε S :=
  ⟨fun h => by simpa using vadd_mem_thickening hS (-c) h, vadd_mem_thickening hS c⟩

/-- **Support ideal.** For an invariant `S` (and an isometric action), `[u] : M → N` factors
through an object of `𝒜_S` if and only if for every `ε > 0`, eventually both endpoint labels of
every nonzero entry of `u_i` lie in the `ε`-thickening of `S`. -/
theorem factorsThrough_supp_iff (hS : ∀ c : ZMod p, ∀ x ∈ S, c +ᵥ x ∈ S) {M N : AsymPre G X}
    (u : M ⟶ N) :
    FiltQuot.ideal (supp S) (AsymCat.mkHom u) ↔
      ∀ ε > 0, ∀ᶠ i in atTop, ∀ a b, FreeCat.mat (AsymPre.coord u i) a b ≠ 0 →
        N.label i a ∈ thickening ε S ∧ M.label i b ∈ thickening ε S := by
  constructor
  · rintro ⟨V, hV, f, g, hfg⟩
    obtain ⟨f, rfl⟩ := AsymCat.mkHom_surjective f
    obtain ⟨g, rfl⟩ := AsymCat.mkHom_surjective g
    rw [← Functor.map_comp, AsymCat.mkHom_eq_iff] at hfg
    intro ε hε
    have h2 : (0 : ℝ) < ε / 2 := half_pos hε
    have hf := (NNReal.tendsto_coe.2 (AsymPre.tendsto_prop f)).eventually (gt_mem_nhds h2)
    have hg := (NNReal.tendsto_coe.2 (AsymPre.tendsto_prop g)).eventually (gt_mem_nhds h2)
    filter_upwards [hfg, hV _ h2, hf, hg] with i hi hVi hfi hgi a b hab
    rw [hi, AsymPre.coord_comp, FreeCat.mat_comp, Matrix.mul_apply] at hab
    obtain ⟨w, -, hw⟩ := Finset.exists_ne_zero_of_sum_ne_zero hab
    have hgw := NNReal.coe_le_coe.2
      (AsymPre.nndist_le_prop (V.as.label i) (N.label i) _ (left_ne_zero_of_mul hw))
    have hfw := NNReal.coe_le_coe.2
      (AsymPre.nndist_le_prop (M.label i) (V.as.label i) _ (right_ne_zero_of_mul hw))
    have hw' : V.as.label i w ∈ thickening (ε / 2) S := vadd_mem_thickening hS _ (hVi w.2)
    obtain ⟨z, hz, hdz⟩ := mem_thickening_iff.1 hw'
    rw [coe_nndist] at hgw hfw
    refine ⟨mem_thickening_iff.2 ⟨z, hz, ?_⟩, mem_thickening_iff.2 ⟨z, hz, ?_⟩⟩
    · have := lt_of_le_of_lt hgw hgi
      linarith [dist_triangle (N.label i a) (V.as.label i w) z]
    · have := lt_of_le_of_lt hfw hfi
      linarith [dist_triangle (M.label i b) (V.as.label i w) z, dist_comm (M.label i b)
        (V.as.label i w)]
  · intro h
    let P : ∀ i, Fin (M.n i) → Prop := fun i k =>
      ∃ (g : G.G i) (a : G.G i × Fin (N.n i)), FreeCat.mat (AsymPre.coord u i) a (g, k) ≠ 0
    refine ⟨⟨M.restrict P⟩, fun ε hε => ?_, AsymCat.mkHom (M.restrictPro P),
      AsymCat.mkHom (M.restrictInc P ≫ u), ?_⟩
    · filter_upwards [h ε hε] with i hi k
      obtain ⟨g, a, hga⟩ := AsymPre.restrictEmb_mem (P := P) k
      exact (vadd_mem_thickening_iff hS _).1 (hi a _ hga).2
    · classical
      rw [← Functor.map_comp, ← Category.assoc, AsymPre.restrictPro_restrictInc,
        AsymPre.trunc_comp_eq]
      exact fun i a b hab => ⟨b.1, a, hab⟩

end HSP
