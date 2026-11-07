import HilbertSmith.Inputs
import HilbertSmith.PadicSubgroups
import HilbertSmith.Interface.Spaces

/-!
# Proposition 5.1 without second countability

OpenAI's Proposition 5.1 (an invariant chart subset; statement 05:14-21, proof 05:23-73) reduces a
faithful action of `ℤ_[p]` on a connected manifold to a faithful action of an open subgroup on a
connected invariant open subset of one chart. OpenAI states §5 for second-countable manifolds
(05:4-6), but the proof never uses second countability. This file proves the reduction without
it, from Newman's theorem in OpenAI's form (`HilbertSmith.NewmanInput`), along OpenAI's proof:

* `HilbertSmith.Interface.exists_forall_fixSet_notMem_nhds` (05:30-50): there is a point `x` such
  that no open subgroup `H_j = p^j ℤ_[p]` fixes a neighbourhood of `x` pointwise. Otherwise the
  interior `F_j` of the fixed set of some `H_j` is nonempty, and it is closed
  (`isClosed_interior_fixSet`): near a point of its closure, Newman's theorem applies to the
  periodic homeomorphisms of the saturation `N' = H_j B` of a small connected `B`.
* `HilbertSmith.Interface.exists_invariant_chart_subset` (05:52-60): for any `x`, an open subgroup
  `H_j` and a connected `H_j`-invariant open `O = H_j B ∋ x` inside the chart at `x`.
* `HilbertSmith.Interface.chartReductionNoSC` (05:61-66): `H_j ≅ ℤ_[p]` acts faithfully on `O`,
  because a nonzero restriction kernel is closed, hence some `H_i`
  (`HilbertSmith.closed_eq_dvd_pow`), and would fix the neighbourhood `O` of `x`. Carried into
  `ℝⁿ` by the chart (`HilbertSmith.Interface.LocalAction.ofChart`), this is a faithful
  `LocalAction` on a connected open set.

The orientation step of Proposition 5.1 (05:68-72) is not proved here: it is assumed, as the
field `HilbertSmith.Interface.Orientation.exists_restrict` of `LocalInputs`.

`ChartReduction`, the form with second countability that the route assumed before this proof,
follows (`chartReduction_of_noSC`).
-/

namespace HilbertSmith.Interface

open Topology Set Filter Pointwise

universe u

/-- **The second-countable form the route assumed before `chartReductionNoSC`**: a faithful
jointly continuous action of `ℤ_[p]` on a connected Hausdorff second-countable `n`-manifold gives
a faithful action of `ℤ_[p]` on a connected open subset of an `n`-dimensional real normed space.
§6 now uses `chartReductionNoSC` instead.

OpenAI's Proposition 5.1 says more: an open subgroup `G ≅ ℤ_[p]` acts faithfully and preserves
orientation on a connected `G`-invariant open subset `O` of a chart of `M`, which is then regarded
as an open subset of `ℝⁿ` (05:16-20). The formal statement drops the subgroup and the chart,
because `Main` uses neither, and orientation preservation, which is the input
`Orientation.exists_restrict`. It is the second-countable case of `ChartReductionNoSC`
(`chartReduction_of_noSC`). -/
def ChartReduction : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (M : Type u) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [ConnectedSpace M]
    [AddAction ℤ_[p] M] [ContinuousVAdd ℤ_[p] M], FaithfulVAdd ℤ_[p] M →
    ∃ A : LocalAction p n, IsConnected A.W ∧ A.Faithful

/-- **What §6 uses of Proposition 5.1, without second countability** (statement 05:14-21, proof
05:23-66; the orientation step 05:68-72 is not part of it): a faithful
jointly continuous action of `ℤ_[p]` on a connected Hausdorff `n`-manifold gives a faithful action
of `ℤ_[p]` on a connected open subset of an `n`-dimensional real normed space. Proved from
`HilbertSmith.NewmanInput` as `chartReductionNoSC`. -/
def ChartReductionNoSC : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [ConnectedSpace M]
    [AddAction ℤ_[p] M] [ContinuousVAdd ℤ_[p] M], FaithfulVAdd ℤ_[p] M →
    ∃ A : LocalAction p n, IsConnected A.W ∧ A.Faithful

/-- The second-countable form is a special case. -/
theorem chartReduction_of_noSC (h : ChartReductionNoSC.{u}) : ChartReduction.{u} :=
  fun p _ n M _ _ _ _ _ _ _ hfaith => h p n M hfaith

/-! ### The open subgroups `H_j = p^j ℤ_[p]` -/

section Subgroups

variable (p : ℕ) [Fact p.Prime]

/-- The open subgroup `H_j = p^j ℤ_[p]` of `ℤ_[p]` (05:35). -/
noncomputable def padicSubgroup (j : ℕ) : AddSubgroup ℤ_[p] :=
  (Ideal.span {(p : ℤ_[p]) ^ j}).toAddSubgroup

variable {p}

/-- `g ∈ H_j` iff `p^j ∣ g`. -/
theorem mem_padicSubgroup {j : ℕ} {g : ℤ_[p]} : g ∈ padicSubgroup p j ↔ (p : ℤ_[p]) ^ j ∣ g :=
  Ideal.mem_span_singleton

/-- `H_j` is open. -/
theorem isOpen_padicSubgroup (j : ℕ) : IsOpen (padicSubgroup p j : Set ℤ_[p]) := by
  convert isOpen_dvd_pow p j using 1
  ext g
  exact mem_padicSubgroup

/-- `H_j` is compact (it is open, hence closed, in the compact `ℤ_[p]`). -/
theorem isCompact_padicSubgroup (j : ℕ) : IsCompact (padicSubgroup p j : Set ℤ_[p]) :=
  (AddSubgroup.isClosed_of_isOpen _ (isOpen_padicSubgroup j)).isCompact

/-- Every neighbourhood of `0` in `ℤ_[p]` contains some `H_j`. -/
theorem exists_padicSubgroup_subset {u : Set ℤ_[p]} (hu : IsOpen u) (h0 : (0 : ℤ_[p]) ∈ u) :
    ∃ j, (padicSubgroup p j : Set ℤ_[p]) ⊆ u := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hu 0 h0
  obtain ⟨j, hj⟩ := PadicInt.exists_pow_neg_lt p hε
  refine ⟨j, fun g hg => hball ?_⟩
  rw [Metric.mem_ball, dist_zero_right]
  exact ((PadicInt.norm_le_pow_iff_mem_span_pow g j).2 hg).trans_lt hj

/-- `p^j ≠ 0` in `ℤ_[p]`. -/
theorem padic_pow_ne_zero (j : ℕ) : (p : ℤ_[p]) ^ j ≠ 0 :=
  pow_ne_zero j (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)

end Subgroups

/-! ### Fixed sets and saturations -/

section Action

variable {p : ℕ} [Fact p.Prime] {M : Type u} [TopologicalSpace M] [AddAction ℤ_[p] M]
  [ContinuousVAdd ℤ_[p] M]

variable (p M) in
/-- The points fixed by every element of `H_j`, `Fix(H_j)` (05:36). -/
def fixSet (j : ℕ) : Set M :=
  {y | ∀ g ∈ padicSubgroup p j, g +ᵥ y = y}

/-- `Fix(H_j)` is closed: "its fixed set is closed" (05:39-40). -/
theorem isClosed_fixSet [T2Space M] (j : ℕ) : IsClosed (fixSet p M j) := by
  simp only [fixSet, ofPred_forall]
  exact isClosed_iInter fun g => isClosed_iInter fun _ =>
    isClosed_eq (continuous_const_vadd g) continuous_id

variable (p) in
/-- The saturation `H_j B = ⋃_{g ∈ H_j} g +ᵥ B` (05:43, 05:58). -/
def saturation (j : ℕ) (B : Set M) : Set M :=
  ⋃ g : padicSubgroup p j, (g : ℤ_[p]) +ᵥ B

omit [TopologicalSpace M] [ContinuousVAdd ℤ_[p] M] in
/-- The points of `H_j B` are the translates `g +ᵥ b`. -/
theorem mem_saturation {j : ℕ} {B : Set M} {y : M} :
    y ∈ saturation p j B ↔ ∃ g ∈ padicSubgroup p j, ∃ b ∈ B, g +ᵥ b = y := by
  simp [saturation, Set.mem_vadd_set]

omit [TopologicalSpace M] [ContinuousVAdd ℤ_[p] M] in
/-- `B ⊆ H_j B`. -/
theorem subset_saturation (j : ℕ) (B : Set M) : B ⊆ saturation p j B := fun b hb =>
  mem_saturation.2 ⟨0, zero_mem _, b, hb, zero_vadd _ b⟩

/-- The saturation of an open set is open: a union of translates (05:43). -/
theorem isOpen_saturation (j : ℕ) {B : Set M} (hB : IsOpen B) : IsOpen (saturation p j B) :=
  isOpen_iUnion fun _ => hB.vadd _

omit [TopologicalSpace M] [ContinuousVAdd ℤ_[p] M] in
/-- The saturation is `H_j`-invariant. -/
theorem vadd_mem_saturation {j : ℕ} {B : Set M} {g : ℤ_[p]} (hg : g ∈ padicSubgroup p j)
    {y : M} (hy : y ∈ saturation p j B) : g +ᵥ y ∈ saturation p j B := by
  obtain ⟨h, hh, b, hb, rfl⟩ := mem_saturation.1 hy
  exact mem_saturation.2 ⟨g + h, add_mem hg hh, b, hb, add_vadd g h b⟩

/-- The saturation of a connected `B ∋ x` with `H_j x ⊆ B` is connected: every translate `gB`
meets `B` at `gx` (05:43-44, 05:60). -/
theorem isConnected_saturation {j : ℕ} {B : Set M} (hB : IsConnected B) {x : M} (hx : x ∈ B)
    (hxB : ∀ g ∈ padicSubgroup p j, g +ᵥ x ∈ B) : IsConnected (saturation p j B) := by
  have hpre : IsPreconnected (⋃ g : padicSubgroup p j, B ∪ ((g : ℤ_[p]) +ᵥ B)) :=
    isPreconnected_iUnion ⟨x, mem_iInter.2 fun _ => Or.inl hx⟩ fun (g : padicSubgroup p j) =>
      IsPreconnected.union ((g : ℤ_[p]) +ᵥ x) (hxB g g.2) (vadd_mem_vadd_set hx)
        hB.isPreconnected (hB.isPreconnected.image _ (continuous_const_vadd _).continuousOn)
  have heq : (⋃ g : padicSubgroup p j, B ∪ ((g : ℤ_[p]) +ᵥ B)) = saturation p j B := by
    rw [← union_iUnion]
    exact union_eq_right.2 (subset_saturation j B)
  exact ⟨(hB.nonempty.mono (subset_saturation j B)), heq ▸ hpre⟩

/-- For `g ∈ H_j`, the homeomorphism `y ↦ g +ᵥ y` of an `H_j`-invariant open set `N`. -/
noncomputable def vaddHomeomorph {j : ℕ} (N : TopologicalSpace.Opens M)
    (hN : ∀ g ∈ padicSubgroup p j, ∀ y ∈ N, g +ᵥ y ∈ N) {g : ℤ_[p]}
    (hg : g ∈ padicSubgroup p j) : N ≃ₜ N where
  toFun y := ⟨g +ᵥ (y : M), hN g hg y y.2⟩
  invFun y := ⟨-g +ᵥ (y : M), hN (-g) (neg_mem hg) y y.2⟩
  left_inv y := Subtype.ext (neg_vadd_vadd g (y : M))
  right_inv y := Subtype.ext (vadd_neg_vadd g (y : M))
  continuous_toFun := ((continuous_const_vadd g).comp continuous_subtype_val).subtype_mk _
  continuous_invFun := ((continuous_const_vadd (-g)).comp continuous_subtype_val).subtype_mk _

/-- The `k`-th iterate of `y ↦ g +ᵥ y` is `y ↦ (k • g) +ᵥ y`. -/
theorem coe_iterate_vaddHomeomorph {j : ℕ} (N : TopologicalSpace.Opens M)
    (hN : ∀ g ∈ padicSubgroup p j, ∀ y ∈ N, g +ᵥ y ∈ N) {g : ℤ_[p]}
    (hg : g ∈ padicSubgroup p j) (k : ℕ) (y : N) :
    (((vaddHomeomorph N hN hg)^[k] y : N) : M) = (k • g) +ᵥ (y : M) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', succ_nsmul', add_vadd, ← ih]
    rfl

end Action

/-! ### The point of Proposition 5.1 -/

section Point

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [AddAction ℤ_[p] M] [ContinuousVAdd ℤ_[p] M]

/-- **`F_j` is closed** (05:38-49). Suppose every point has a neighbourhood fixed pointwise by some
`H_ℓ`. Let `x` be in the closure of `F_j = int Fix(H_j)`; then `H_j` fixes `x`. Take `ℓ` with
`Fix(H_ℓ)` a neighbourhood of `x`; compactness of `H_j` gives a connected open `B ∋ x` with
`H_j B ⊆ int Fix(H_ℓ)`. The saturation `N' = H_j B` is open, connected and `H_j`-invariant, and
each `g ∈ H_j` acts on it by a homeomorphism of order dividing `p^ℓ` (the action factors through
`H_j / (H_j ∩ H_ℓ)`) that fixes the nonempty open set `N' ∩ F_j`. Newman's theorem makes it the
identity on `N'`, so `x ∈ F_j`. -/
theorem isClosed_interior_fixSet [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (hN : NewmanInput.{u}) (hsup : ∀ y : M, ∃ ℓ, fixSet p M ℓ ∈ 𝓝 y)
    (j : ℕ) : IsClosed (interior (fixSet p M j)) := by
  have : LocallyConnectedSpace M :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin n)) M
  refine isClosed_of_closure_subset fun x hx => ?_
  -- `H_j` fixes `x`, since its fixed set is closed.
  have hxfix : x ∈ fixSet p M j :=
    (isClosed_fixSet j).closure_subset (closure_mono interior_subset hx)
  obtain ⟨ℓ, hℓ⟩ := hsup x
  -- Compactness of `H_j`: a connected open `B ∋ x` with `H_j B ⊆ int Fix(H_ℓ)` (05:41-43).
  have hn : IsOpen ((fun q : ℤ_[p] × M => q.1 +ᵥ q.2) ⁻¹' interior (fixSet p M ℓ)) :=
    isOpen_interior.preimage continuous_vadd
  obtain ⟨u, v, -, hv, hHu, hxv, huv⟩ := generalized_tube_lemma (isCompact_padicSubgroup j)
    isCompact_singleton hn (by
      rintro ⟨g, y⟩ ⟨hg, hy⟩
      rw [mem_singleton_iff] at hy
      subst hy
      change g +ᵥ x ∈ interior (fixSet p M ℓ)
      rw [hxfix g hg]
      exact mem_interior_iff_mem_nhds.2 hℓ)
  obtain ⟨B, ⟨hBo, hxB, hBc⟩, hBv⟩ :=
    (LocallyConnectedSpace.open_connected_basis x).mem_iff.1 (hv.mem_nhds (hxv rfl))
  -- The saturation `N' = H_j B`.
  have hNo : IsOpen (saturation p j B) := isOpen_saturation j hBo
  have hNc : IsConnected (saturation p j B) :=
    isConnected_saturation hBc hxB fun g hg => by rw [hxfix g hg]; exact hxB
  have hxN : x ∈ saturation p j B := subset_saturation j B hxB
  have hNℓ : saturation p j B ⊆ fixSet p M ℓ := by
    intro y hy
    obtain ⟨g, hg, b, hb, rfl⟩ := mem_saturation.1 hy
    exact interior_subset (huv (mk_mem_prod (hHu hg) (hBv hb)))
  -- Newman's theorem on `N'`, for each `g ∈ H_j`.
  have key : ∀ g ∈ padicSubgroup p j, ∀ y ∈ saturation p j B, g +ᵥ y = y := by
    intro g hg
    let N' : TopologicalSpace.Opens M := ⟨saturation p j B, hNo⟩
    have : ConnectedSpace N' := isConnected_iff_connectedSpace.1 hNc
    let f := vaddHomeomorph N' (fun _ hh _ hy => vadd_mem_saturation hh hy) hg
    obtain ⟨z, hzN, hzF⟩ := mem_closure_iff.1 hx _ hNo hxN
    have hid := hN n N' f (p ^ ℓ) (pow_pos (Fact.out : p.Prime).pos ℓ)
      (fun y => Subtype.ext <| by
        rw [coe_iterate_vaddHomeomorph]
        refine hNℓ y.2 _ (mem_padicSubgroup.2 ?_)
        rw [nsmul_eq_mul, Nat.cast_pow]
        exact dvd_mul_right _ _)
      {y : N' | (y : M) ∈ interior (fixSet p M j)}
      (isOpen_interior.preimage continuous_subtype_val) ⟨⟨z, hzN⟩, hzF⟩
      (fun y hy => Subtype.ext (interior_subset hy g hg))
    exact fun y hy => congrArg Subtype.val (hid ⟨y, hy⟩)
  exact mem_interior.2 ⟨saturation p j B, fun y hy g hg => key g hg y hy, hNo, hxN⟩

/-- **The point of Proposition 5.1** (05:30-50): for a faithful action on a connected manifold,
some point has no neighbourhood fixed pointwise by an open subgroup `H_ℓ`. Otherwise some `F_j`
is nonempty, and closed by `isClosed_interior_fixSet`, so it is all of `M`, and `p^j ≠ 0` acts
trivially. -/
theorem exists_forall_fixSet_notMem_nhds [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [ConnectedSpace M] (hN : NewmanInput.{u})
    (hfaith : FaithfulVAdd ℤ_[p] M) : ∃ x : M, ∀ ℓ, fixSet p M ℓ ∉ 𝓝 x := by
  by_contra! hsup
  obtain ⟨x₀⟩ := (inferInstance : Nonempty M)
  obtain ⟨j, hj⟩ := hsup x₀
  have huniv : interior (fixSet p M j) = univ :=
    IsClopen.eq_univ ⟨isClosed_interior_fixSet (n := n) hN hsup j, isOpen_interior⟩
      ⟨x₀, mem_interior_iff_mem_nhds.2 hj⟩
  refine padic_pow_ne_zero (p := p) j (hfaith.eq_of_vadd_eq_vadd fun y => ?_)
  rw [zero_vadd]
  have hy : y ∈ interior (fixSet p M j) := huniv ▸ mem_univ y
  exact interior_subset hy _ (mem_padicSubgroup.2 dvd_rfl)

/-- **The invariant chart subset** (05:52-60): for every `x`, there are `j` and a connected
`H_j`-invariant open `O ∋ x` inside the chart at `x`. Take a connected open `B ∋ x` with compact
closure in the chart; joint continuity and compactness of `closure B` give `H_j` with
`H_j (closure B)` in the chart and `H_j x ⊆ B`; then `O = H_j B`. -/
theorem exists_invariant_chart_subset [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (x : M) :
    ∃ j, ∃ O : Set M, IsOpen O ∧ IsConnected O ∧ x ∈ O ∧
      O ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) x).source ∧
      ∀ g ∈ padicSubgroup p j, ∀ y ∈ O, g +ᵥ y ∈ O := by
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  have : LocallyConnectedSpace M :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin n)) M
  set C := (chartAt (EuclideanSpace ℝ (Fin n)) x).source
  obtain ⟨K, hK, hxK, hKC⟩ :=
    exists_compact_subset (chartAt (EuclideanSpace ℝ (Fin n)) x).open_source (mem_chart_source _ x)
  obtain ⟨B, ⟨hBo, hxB, hBc⟩, hBK⟩ :=
    (LocallyConnectedSpace.open_connected_basis x).mem_iff.1 (mem_interior_iff_mem_nhds.1 hxK)
  have hcl : closure B ⊆ K := closure_minimal hBK hK.isClosed
  -- A neighbourhood `u` of `0` with `u +ᵥ closure B ⊆ C` (05:53-54).
  have hn : IsOpen ((fun q : ℤ_[p] × M => q.1 +ᵥ q.2) ⁻¹' C) :=
    (chartAt (EuclideanSpace ℝ (Fin n)) x).open_source.preimage continuous_vadd
  obtain ⟨u, v, hu, -, hu0, hv, huv⟩ := generalized_tube_lemma isCompact_singleton
    (hK.of_isClosed_subset isClosed_closure hcl) hn (by
      rintro ⟨g, y⟩ ⟨hg, hy⟩
      rw [mem_singleton_iff] at hg
      subst hg
      exact show (0 : ℤ_[p]) +ᵥ y ∈ C by rw [zero_vadd]; exact hKC (hcl hy))
  -- A neighbourhood of `0` moving `x` inside `B` (05:55).
  have hu' : IsOpen {g : ℤ_[p] | g +ᵥ x ∈ B} := hBo.preimage (continuous_id.vadd continuous_const)
  obtain ⟨j, hj⟩ := exists_padicSubgroup_subset (hu.inter hu')
    ⟨hu0 rfl, by simpa only [mem_ofPred_eq, zero_vadd] using hxB⟩
  refine ⟨j, saturation p j B, isOpen_saturation j hBo,
    isConnected_saturation hBc hxB fun g hg => (hj hg).2, subset_saturation j B hxB, ?_,
    fun g hg y hy => vadd_mem_saturation hg hy⟩
  intro y hy
  obtain ⟨g, hg, b, hb, rfl⟩ := mem_saturation.1 hy
  exact huv (mk_mem_prod (hj hg).1 (hv (subset_closure hb)))

end Point

/-! ### The action on the chart subset -/

section ChartAction

variable {p : ℕ} [Fact p.Prime] {M : Type u} [TopologicalSpace M] [AddAction ℤ_[p] M]
  [ContinuousVAdd ℤ_[p] M]

/-- The action of `H_j`, identified with `ℤ_[p]` by `a ↦ p^j a`, on an `H_j`-invariant set `O`. -/
@[instance_reducible]
noncomputable def subgroupAct (j : ℕ) (O : Set M)
    (hO : ∀ g ∈ padicSubgroup p j, ∀ y ∈ O, g +ᵥ y ∈ O) : AddAction ℤ_[p] O where
  vadd a y :=
    ⟨((p : ℤ_[p]) ^ j * a) +ᵥ (y : M), hO _ (mem_padicSubgroup.2 (dvd_mul_right _ _)) y y.2⟩
  zero_vadd y := Subtype.ext <| show ((p : ℤ_[p]) ^ j * 0) +ᵥ (y : M) = y by
    rw [mul_zero, zero_vadd]
  add_vadd a b y := Subtype.ext <| show ((p : ℤ_[p]) ^ j * (a + b)) +ᵥ (y : M) =
      ((p : ℤ_[p]) ^ j * a) +ᵥ (((p : ℤ_[p]) ^ j * b) +ᵥ (y : M)) by
    rw [mul_add, add_vadd]

/-- The action of `H_j` on `O` is jointly continuous. -/
theorem continuousVAdd_subgroupAct (j : ℕ) (O : Set M)
    (hO : ∀ g ∈ padicSubgroup p j, ∀ y ∈ O, g +ᵥ y ∈ O) :
    letI := subgroupAct j O hO
    ContinuousVAdd ℤ_[p] O := by
  have h : Continuous fun q : ℤ_[p] × O => (⟨((p : ℤ_[p]) ^ j * q.1) +ᵥ (q.2 : M),
      hO _ (mem_padicSubgroup.2 (dvd_mul_right _ _)) q.2 q.2.2⟩ : O) :=
    (continuous_vadd.comp ((continuous_const.mul continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd))).subtype_mk _
  exact @ContinuousVAdd.mk _ _ (subgroupAct j O hO).toVAdd _ _ h

end ChartAction

section ChartImage

variable {p : ℕ} [Fact p.Prime] {M : Type u} [TopologicalSpace M] {n : ℕ}

/-- **The local action on the chart image** of an open set `O` inside the source of a chart `e`,
with an action of `ℤ_[p]` on `O`: the chart carries `O` homeomorphically onto the open set
`e(O) ⊆ ℝⁿ` (05:19-20: "we may regard `O` as the actual open subset of `ℝⁿ`"), and the action
with it. -/
noncomputable def LocalAction.ofChart (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (O : Set M) (hO : IsOpen O) (hOe : O ⊆ e.source) [AddAction ℤ_[p] O]
    [ContinuousVAdd ℤ_[p] O] : LocalAction p n where
  E := EuclideanSpace ℝ (Fin n)
  finrank_eq := finrank_euclideanSpace_fin
  W := e '' O
  isOpen := e.isOpen_image_of_subset_source hO hOe
  act := (e.homeomorphOfImageSubsetSource hOe rfl).symm.toEquiv.addAction ℤ_[p]
  cont := by
    let φ := e.homeomorphOfImageSubsetSource hOe rfl
    exact @ContinuousVAdd.mk _ _ (φ.symm.toEquiv.addAction ℤ_[p]).toVAdd _ _
      (φ.continuous.comp (continuous_vadd.comp
        (continuous_fst.prodMk (φ.symm.continuous.comp continuous_snd))))

/-- The chart image of a connected `O` is connected. -/
theorem LocalAction.ofChart_isConnected (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    {O : Set M} (hO : IsOpen O) (hOe : O ⊆ e.source) [AddAction ℤ_[p] O] [ContinuousVAdd ℤ_[p] O]
    (hc : IsConnected O) : IsConnected (LocalAction.ofChart (p := p) e O hO hOe).W :=
  hc.image e (e.continuousOn.mono hOe)

/-- A faithful action on `O` gives a faithful local action on its chart image. -/
theorem LocalAction.ofChart_faithful (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    {O : Set M} (hO : IsOpen O) (hOe : O ⊆ e.source) [AddAction ℤ_[p] O] [ContinuousVAdd ℤ_[p] O]
    [FaithfulVAdd ℤ_[p] O] : (LocalAction.ofChart (p := p) e O hO hOe).Faithful := by
  let φ := e.homeomorphOfImageSubsetSource hOe rfl
  refine ⟨fun {a b} h => FaithfulVAdd.eq_of_vadd_eq_vadd fun y => φ.injective ?_⟩
  have hy := h (φ y)
  change φ (a +ᵥ φ.symm (φ y)) = φ (b +ᵥ φ.symm (φ y)) at hy
  rwa [φ.symm_apply_apply] at hy

end ChartImage

/-! ### The reduction -/

/-- **Proposition 5.1 without second countability**, from Newman's theorem (05:23-66): a
faithful action of `ℤ_[p]` on a connected Hausdorff `n`-manifold gives a faithful `LocalAction` on
a connected open subset of `ℝⁿ`. Take the point `x` of `exists_forall_fixSet_notMem_nhds` and the
invariant chart subset `O = H_j B` of `exists_invariant_chart_subset`. The restriction kernel of
`H_j ≅ ℤ_[p]` on `O` is a closed subgroup; if it were nonzero it would be some `p^i ℤ_[p]`
(`HilbertSmith.closed_eq_dvd_pow`, 05:61-64), and `H_{i+j}` would fix the neighbourhood `O` of
`x`. So `H_j` acts faithfully on `O`, and the chart carries the action into `ℝⁿ`. -/
theorem chartReductionNoSC (hN : NewmanInput.{u}) : ChartReductionNoSC.{u} := by
  intro p _ n M _ _ _ _ _ _ hfaith
  obtain ⟨x, hx⟩ := exists_forall_fixSet_notMem_nhds (n := n) hN hfaith
  obtain ⟨j, O, hOo, hOc, hxO, hOC, hOinv⟩ := exists_invariant_chart_subset (p := p) (n := n) x
  -- The restriction kernel, in the coordinate `a ↦ p^j a` of `H_j`.
  let K : AddSubgroup ℤ_[p] :=
    { carrier := {a | ∀ y ∈ O, ((p : ℤ_[p]) ^ j * a) +ᵥ y = y}
      add_mem' := fun {a b} ha hb y hy => by rw [mul_add, add_vadd, hb y hy, ha y hy]
      zero_mem' := fun y _ => by rw [mul_zero, zero_vadd]
      neg_mem' := fun {a} ha y hy => by
        conv_lhs => rw [← ha y hy]
        rw [← add_vadd, ← mul_add, neg_add_cancel, mul_zero, zero_vadd] }
  have hKc : IsClosed (K : Set ℤ_[p]) := by
    change IsClosed {a : ℤ_[p] | ∀ y ∈ O, ((p : ℤ_[p]) ^ j * a) +ᵥ y = y}
    simp only [ofPred_forall]
    exact isClosed_iInter fun y => isClosed_iInter fun _ =>
      isClosed_eq ((continuous_const.mul continuous_id).vadd continuous_const) continuous_const
  have hK : K = ⊥ := by
    by_contra hne
    obtain ⟨i, hi⟩ := closed_eq_dvd_pow p hKc hne
    refine hx (i + j) (mem_of_superset (hOo.mem_nhds hxO) fun y hy g hg => ?_)
    obtain ⟨c, rfl⟩ := mem_padicSubgroup.1 hg
    have hc : (p : ℤ_[p]) ^ i * c ∈ K := (hi _).2 (dvd_mul_right _ _)
    have e : (p : ℤ_[p]) ^ (i + j) * c = (p : ℤ_[p]) ^ j * ((p : ℤ_[p]) ^ i * c) := by ring
    rw [e]
    exact hc y hy
  let _ : AddAction ℤ_[p] O := subgroupAct j O hOinv
  have : ContinuousVAdd ℤ_[p] O := continuousVAdd_subgroupAct j O hOinv
  have : FaithfulVAdd ℤ_[p] O := ⟨fun {a b} hab => by
    have hmem : a - b ∈ K := fun y hy => by
      have h := congrArg Subtype.val (hab ⟨y, hy⟩)
      change ((p : ℤ_[p]) ^ j * a) +ᵥ y = ((p : ℤ_[p]) ^ j * b) +ᵥ y at h
      rw [show (p : ℤ_[p]) ^ j * (a - b) = -((p : ℤ_[p]) ^ j * b) + (p : ℤ_[p]) ^ j * a by ring,
        add_vadd, h, neg_vadd_vadd]
    rw [hK, AddSubgroup.mem_bot, sub_eq_zero] at hmem
    exact hmem⟩
  exact ⟨LocalAction.ofChart (p := p) _ O hOo hOC, LocalAction.ofChart_isConnected _ hOo hOC hOc,
    LocalAction.ofChart_faithful _ hOo hOC⟩

end HilbertSmith.Interface
