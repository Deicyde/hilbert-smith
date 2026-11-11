import Mathlib
import HilbertSmithPaper.LocalData.Subgroups.FixedSetsClosed
import HilbertSmithPaper.LocalData.Subgroups.PadicSubgroupsBasis
import HilbertSmithPaper.Inputs.Newman.NewmanOpenSet

/-!
# Interiors of fixed sets are closed

Let `ℤ_[p]` act jointly continuously on an `n`-manifold `M` (Hausdorff, charted on
`EuclideanSpace ℝ (Fin n)`) such that every point has a neighbourhood fixed pointwise by some `H_m`.
Then every `F_j = interior (Fix_j M)` is closed.

For `x ∈ closure F_j`: `x ∈ Fix_j` (fixed sets are closed); `x ∈ N = interior (Fix_m M)` for some
`m`; the tube lemma for the compact `H_j` gives a connected open `B ∋ x` (a connected component, `M`
being locally connected) with `H_j +ᵥ B ⊆ N`. The saturation `N' = ⋃_{a ∈ H_j} a +ᵥ B` is open,
`H_j`-invariant and connected (every translate contains `x`), so a connected `n`-manifold. Each
`a ∈ H_j` restricts to a homeomorphism of `N'` whose `p^m`-th iterate is `p^m • a ∈ H_m`, the
identity on `N ⊇ N'`, and which fixes the nonempty open set `N' ∩ F_j`. Newman's theorem makes it
the identity, so `N' ⊆ Fix_j` and `x ∈ F_j`.
-/

open Topology Pointwise

namespace HSP

/-- If every point has a neighbourhood fixed by some `H_m`, the interiors of the fixed sets are
closed. -/
theorem isClosed_interior_fixSet {p : ℕ} [Fact p.Prime] {n : ℕ} {M : Type*} [TopologicalSpace M]
    [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [AddAction ℤ_[p] M]
    [ContinuousVAdd ℤ_[p] M] (h : ∀ y : M, ∃ m, fixSet p M m ∈ 𝓝 y) (j : ℕ) :
    IsClosed (interior (fixSet p M j)) := by
  have : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin n)) M
  rw [← closure_subset_iff_isClosed]
  intro x hx
  -- step 1: `x` is fixed by `H_j`
  have hxfix : x ∈ fixSet p M j :=
    closure_minimal interior_subset (isClosed_fixSet j) hx
  -- step 2: `x ∈ N`
  obtain ⟨m, hm⟩ := h x
  set N := interior (fixSet p M m) with hNdef
  have hxN : x ∈ N := mem_interior_iff_mem_nhds.2 hm
  -- step 3: the tube lemma
  set Hj : Set ℤ_[p] := (padicSubgroup p j : Set ℤ_[p])
  have hHc : IsCompact Hj := ((padicSubgroup_basis p).1 j).2
  have hopen : IsOpen {q : ℤ_[p] × M | q.1 +ᵥ q.2 ∈ N} :=
    isOpen_interior.preimage continuous_vadd
  have hsub : Hj ×ˢ ({x} : Set M) ⊆ {q : ℤ_[p] × M | q.1 +ᵥ q.2 ∈ N} := by
    rintro ⟨a, y⟩ ⟨ha, hy⟩
    simp only [Set.mem_singleton_iff] at hy
    subst hy
    simpa [hxfix a ha] using hxN
  obtain ⟨u, v, -, hv, hHu, hxv, huv⟩ :=
    generalized_tube_lemma hHc isCompact_singleton hopen hsub
  set B := connectedComponentIn v x
  have hBo : IsOpen B := hv.connectedComponentIn
  have hxB : x ∈ B := mem_connectedComponentIn (hxv rfl)
  have hBv : B ⊆ v := connectedComponentIn_subset v x
  have hBc : IsPreconnected B := isPreconnected_connectedComponentIn
  -- step 4: the saturation
  set N' : Set M := ⋃ a ∈ Hj, a +ᵥ B with hN'def
  have hN'o : IsOpen N' := isOpen_biUnion fun a _ => hBo.vadd a
  have hxN' : x ∈ N' := Set.mem_biUnion (padicSubgroup p j).zero_mem
    (by simpa using hxB)
  have hN'N : N' ⊆ N := by
    intro y hy
    obtain ⟨a, ha, hy'⟩ := Set.mem_iUnion₂.1 hy
    obtain ⟨b, hb, rfl⟩ := Set.mem_vadd_set.1 hy'
    exact huv (Set.mk_mem_prod (hHu ha) (hBv hb))
  have hN'inv : ∀ c ∈ Hj, ∀ y ∈ N', c +ᵥ y ∈ N' := by
    intro c hc y hy
    obtain ⟨a, ha, hy'⟩ := Set.mem_iUnion₂.1 hy
    obtain ⟨b, hb, rfl⟩ := Set.mem_vadd_set.1 hy'
    rw [vadd_vadd]
    exact Set.mem_biUnion ((padicSubgroup p j).add_mem hc ha) (Set.vadd_mem_vadd_set hb)
  have hN'conn : IsConnected N' := by
    refine ⟨⟨x, hxN'⟩, ?_⟩
    have : N' = ⋃₀ ((fun a : ℤ_[p] => a +ᵥ B) '' Hj) := by
      simp only [N', Set.sUnion_image]
    rw [this]
    refine isPreconnected_sUnion x _ ?_ ?_
    · rintro _ ⟨a, ha, rfl⟩
      have : a +ᵥ x ∈ a +ᵥ B := Set.vadd_mem_vadd_set hxB
      rwa [hxfix a ha] at this
    · rintro _ ⟨a, -, rfl⟩
      show IsPreconnected (a +ᵥ B)
      rw [← Set.image_vadd]
      exact hBc.image _ (continuous_const_vadd a).continuousOn
  -- step 5: the manifold `N'` and the homeomorphisms
  let O : TopologicalSpace.Opens M := ⟨N', hN'o⟩
  have : ConnectedSpace O := isConnected_iff_connectedSpace.1 hN'conn
  have hfixes : ∀ a ∈ Hj, ∀ y ∈ N', a +ᵥ y = y := by
    intro a ha
    let f : O ≃ₜ O :=
      { toFun := fun y => ⟨a +ᵥ (y : M), hN'inv a ha y y.2⟩
        invFun := fun y => ⟨-a +ᵥ (y : M), hN'inv (-a) ((padicSubgroup p j).neg_mem ha) y y.2⟩
        left_inv := fun y => Subtype.ext (neg_vadd_vadd a (y : M))
        right_inv := fun y => Subtype.ext (vadd_neg_vadd a (y : M))
        continuous_toFun :=
          ((continuous_const_vadd a).comp continuous_subtype_val).subtype_mk _
        continuous_invFun :=
          ((continuous_const_vadd (-a)).comp continuous_subtype_val).subtype_mk _ }
    have hiter : ∀ k : ℕ, ∀ y : O, (((⇑f)^[k] y : O) : M) = (k • a) +ᵥ (y : M) := by
      intro k
      induction k with
      | zero => intro y; simp
      | succ k ih =>
        intro y
        rw [Function.iterate_succ_apply', succ_nsmul', ← vadd_vadd]
        change a +ᵥ (((⇑f)^[k] y : O) : M) = _
        rw [ih]
    have hper : (⇑f)^[p ^ m] = id := by
      funext y
      apply Subtype.ext
      rw [hiter]
      have hmem : (p ^ m) • a ∈ padicSubgroup p m := by
        change (p : ℤ_[p]) ^ m ∣ (p ^ m) • a
        rw [nsmul_eq_mul]
        push_cast
        exact dvd_mul_right _ _
      exact interior_subset (hN'N y.2) _ hmem
    have hU : IsOpen {y : O | (y : M) ∈ interior (fixSet p M j)} :=
      isOpen_interior.preimage continuous_subtype_val
    have hUne : {y : O | (y : M) ∈ interior (fixSet p M j)}.Nonempty := by
      obtain ⟨y, hyN', hyF⟩ := mem_closure_iff.1 hx N' hN'o hxN'
      exact ⟨⟨y, hyN'⟩, hyF⟩
    have hid := newman_open_set (n := n) f (p ^ m)
      (Nat.one_le_pow _ _ (Fact.out : p.Prime).pos) hper
      _ hU hUne fun y hy => Subtype.ext (interior_subset hy a ha)
    intro y hy
    have := congrFun hid ⟨y, hy⟩
    exact congrArg Subtype.val this
  -- step 6: conclusion
  exact interior_maximal (fun y hy a ha => hfixes a ha y hy) hN'o hxN'

end HSP
