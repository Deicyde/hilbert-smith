import Mathlib
import HilbertSmithPaper.Signatures.Forms.SignatureSplitting

/-!
# Invariant signature splittings exist

Let `W` be a finite-dimensional real vector space, `b` a nondegenerate symmetric bilinear form on
`W`, and `ρ` a representation of a finite group `G` on `W` by `b`-isometries. Then `(W, b, ρ)` has
a signature splitting (`IsSignatureSplitting`).

Proof: averaging a positive definite form over `G` gives a `ρ`-invariant inner product (put on
`W` locally through `InnerProductSpace.Core`). The operator `B` with `⟪B y, z⟫ = b z y` is
symmetric, injective and commutes with `G`. In an orthonormal eigenbasis `v i` of `B` (eigenvalues
`μ i`, all nonzero), `V⁺` (resp. `V⁻`) is the set of vectors whose coordinates vanish where
`μ i ≤ 0` (resp. `μ i ≥ 0`); `b x x = Σ μ i ⟪v i, x⟫²` gives definiteness, and invariance holds
because `ρ g⁻¹` preserves each eigenspace.
-/

namespace HSP

open Module
open scoped RealInnerProductSpace

variable {G W : Type*} [AddCommGroup W] [Module ℝ W]

/-- **Invariant signature splittings exist.** A nondegenerate symmetric bilinear form on a
finite-dimensional real vector space, invariant under a representation of a finite group, has a
signature splitting. -/
theorem exists_signatureSplitting [Group G] [Finite G] [FiniteDimensional ℝ W]
    (b : LinearMap.BilinForm ℝ W) (ρ : Representation ℝ G W) (hb : b.IsSymm)
    (hnd : b.Nondegenerate) (hρ : ∀ g x y, b (ρ g x) (ρ g y) = b x y) :
    ∃ Vp Vn : Submodule ℝ W, IsSignatureSplitting b ρ Vp Vn := by
  classical
  have : Fintype G := Fintype.ofFinite G
  have hρinv : ∀ g x, ρ g (ρ g⁻¹ x) = x := fun g x => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  -- Step 1: a `ρ`-invariant inner product, by averaging.
  obtain ⟨core, hcore⟩ : ∃ core : InnerProductSpace.Core ℝ W,
      ∀ g x y, core.inner (ρ g x) (ρ g y) = core.inner x y := by
    let c := (Module.finBasis ℝ W).equivFun
    let ip : W → W → ℝ := fun x y => ∑ g : G, ∑ i, c (ρ g x) i * c (ρ g y) i
    have hnonneg : ∀ x, 0 ≤ ip x x := fun x =>
      Finset.sum_nonneg fun g _ => Finset.sum_nonneg fun i _ => mul_self_nonneg _
    have hpos : ∀ x, x ≠ 0 → 0 < ip x x := by
      intro x hx
      have h1 : 0 < ∑ i, c x i * c x i := by
        obtain ⟨i, hi⟩ : ∃ i, c x i ≠ 0 := by
          by_contra! h
          exact hx (c.injective (by ext i; simp [h i]))
        exact lt_of_lt_of_le (mul_self_pos.2 hi)
          (Finset.single_le_sum (f := fun j => c x j * c x j) (fun j _ => mul_self_nonneg _)
            (Finset.mem_univ i))
      refine lt_of_lt_of_le (by simpa using h1)
        (Finset.single_le_sum (f := fun g : G => ∑ i, c (ρ g x) i * c (ρ g x) i)
          (fun g _ => Finset.sum_nonneg fun i _ => mul_self_nonneg _) (Finset.mem_univ 1))
    refine ⟨{ inner := ip
              conj_inner_symm := fun x y => by
                simp only [conj_trivial, ip, mul_comm]
              re_inner_nonneg := fun x => by simpa using hnonneg x
              add_left := fun x y z => by
                simp only [ip, map_add, Pi.add_apply, add_mul, Finset.sum_add_distrib]
              smul_left := fun x y r => by
                simp only [ip, map_smul, Pi.smul_apply, smul_eq_mul, conj_trivial, Finset.mul_sum,
                  mul_assoc]
              definite := fun x hx => by
                by_contra h
                exact (hpos x h).ne' hx }, ?_⟩
    intro h x y
    show ∑ g : G, ∑ i, c (ρ g (ρ h x)) i * c (ρ g (ρ h y)) i =
      ∑ g : G, ∑ i, c (ρ g x) i * c (ρ g y) i
    simp only [← Module.End.mul_apply, ← map_mul]
    exact Fintype.sum_equiv (Equiv.mulRight h) _ _ (fun g => rfl)
  let : NormedAddCommGroup W := @InnerProductSpace.Core.toNormedAddCommGroup ℝ W _ _ _ core
  let : InnerProductSpace ℝ W := InnerProductSpace.ofCore core.toCore
  have hinv : ∀ g x y, ⟪ρ g x, ρ g y⟫ = ⟪x, y⟫ := hcore
  -- Step 2: the operator `B` with `⟪B y, z⟫ = b z y`.
  let P : LinearMap.BilinForm ℝ W := innerₗ W
  have hP : P.Nondegenerate :=
    ⟨fun m hm => inner_self_eq_zero.1 (hm m), fun m hm => inner_self_eq_zero.1 (hm m)⟩
  let B : W →ₗ[ℝ] W := (P.toDual hP).symm.toLinearMap ∘ₗ b.flip
  have hB : ∀ y z, ⟪B y, z⟫ = b z y := by
    intro y z
    change P ((P.toDual hP).symm (b.flip y)) z = _
    rw [← LinearMap.BilinForm.toDual_def hP, LinearEquiv.apply_symm_apply]
    rfl
  have hBsym : B.IsSymmetric := by
    intro x y
    rw [hB, real_inner_comm, hB, hb.eq]
  have hBcomm : ∀ g y, B (ρ g y) = ρ g (B y) := by
    intro g y
    refine ext_inner_right ℝ fun z => ?_
    rw [hB, ← hρinv g z, hρ, ← hB, hinv]
  have hBinj : ∀ y, B y = 0 → y = 0 := by
    intro y hy
    refine hnd.1 y fun z => ?_
    rw [hb.eq, ← hB, hy, inner_zero_left]
  -- Step 3: the spectral theorem.
  set n := finrank ℝ W
  set v := hBsym.eigenvectorBasis (rfl : finrank ℝ W = n)
  set μ := hBsym.eigenvalues (rfl : finrank ℝ W = n)
  have hv : ∀ i, B (v i) = μ i • v i := fun i =>
    hBsym.apply_eigenvectorBasis (rfl : finrank ℝ W = n) i
  have hμ : ∀ i, μ i ≠ 0 := by
    intro i h
    have : B (v i) = 0 := by rw [hv, h, zero_smul]
    exact v.orthonormal.ne_zero i (hBinj _ this)
  have hquad : ∀ x, b x x = ∑ i, μ i * (⟪v i, x⟫ * ⟪v i, x⟫) := by
    intro x
    rw [← hB, ← v.sum_inner_mul_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hBsym, hv, inner_smul_right, real_inner_comm]
    ring
  have hzero : ∀ x, (∀ i, ⟪v i, x⟫ = 0) → x = 0 := by
    intro x hx
    rw [← v.sum_repr' x]
    simp [hx]
  -- the subspaces `K S = {x | ⟪v i, x⟫ = 0 for i ∈ S}`
  let K : (Fin n → Prop) → Submodule ℝ W := fun S =>
    { carrier := {x | ∀ i, S i → ⟪v i, x⟫ = 0}
      add_mem' := fun {x y} hx hy i hi => by rw [inner_add_right, hx i hi, hy i hi, add_zero]
      zero_mem' := fun i _ => inner_zero_right _
      smul_mem' := fun r x hx i hi => by rw [inner_smul_right, hx i hi, mul_zero] }
  have hK : ∀ S : Fin n → Prop, (∀ i j, S i → μ j = μ i → S j) → ∀ g, ∀ x ∈ K S, ρ g x ∈ K S := by
    intro S hS g x hx i hi
    set y := ρ g⁻¹ (v i)
    have hy : B y = μ i • y := by rw [hBcomm, hv, map_smul]
    rw [← hρinv g (v i), hinv, ← v.sum_inner_mul_inner]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : S j
    · rw [hx j hj, mul_zero]
    · have hne : μ j ≠ μ i := fun h => hj (hS i j hi h)
      have : (μ i - μ j) * ⟪v j, y⟫ = 0 := by
        have h1 : ⟪v j, B y⟫ = μ i * ⟪v j, y⟫ := by rw [hy, inner_smul_right]
        have h2 : ⟪v j, B y⟫ = μ j * ⟪v j, y⟫ := by rw [← hBsym, hv, inner_smul_left]; simp
        rw [sub_mul]; linarith
      rcases mul_eq_zero.1 this with h | h
      · exact absurd (sub_eq_zero.1 h).symm hne
      · rw [real_inner_comm, h, zero_mul]
  refine ⟨K fun i => μ i ≤ 0, K fun i => 0 ≤ μ i,
    { mapsTo_pos := hK _ fun i j hi h => h ▸ hi
      mapsTo_neg := hK _ fun i j hi h => h ▸ hi
      isCompl := ?_
      pos := ?_
      neg := ?_ }⟩
  · constructor
    · rw [Submodule.disjoint_def]
      intro x hp hn
      exact hzero x fun i => (le_total (μ i) 0).elim (hp i) (hn i)
    · rw [codisjoint_iff, eq_top_iff]
      intro x _
      have hsplit : x = (∑ i, (if 0 < μ i then ⟪v i, x⟫ else 0) • v i) +
          ∑ i, (if 0 < μ i then 0 else ⟪v i, x⟫) • v i := by
        conv_lhs => rw [← v.sum_repr' x]
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        split_ifs <;> simp
      rw [hsplit]
      refine Submodule.add_mem_sup (fun i hi => ?_) (fun i hi => ?_)
      · rw [v.orthonormal.inner_right_fintype, ite_eq_right (not_lt.2 hi)]
      · rw [v.orthonormal.inner_right_fintype,
          ite_eq_left (lt_of_le_of_ne hi (hμ i).symm)]
  · intro x hx h0
    rw [hquad]
    obtain ⟨i, hi⟩ : ∃ i, ⟪v i, x⟫ ≠ 0 := by
      by_contra! h
      exact h0 (hzero x h)
    refine Finset.sum_pos' (fun j _ => ?_) ⟨i, Finset.mem_univ _, ?_⟩
    · by_cases hj : μ j ≤ 0
      · rw [hx j hj]; simp
      · exact mul_nonneg (not_le.1 hj).le (mul_self_nonneg _)
    · have : 0 < μ i := not_le.1 fun h => hi (hx i h)
      exact mul_pos this (mul_self_pos.2 hi)
  · intro x hx h0
    rw [hquad, ← neg_pos, ← Finset.sum_neg_distrib]
    obtain ⟨i, hi⟩ : ∃ i, ⟪v i, x⟫ ≠ 0 := by
      by_contra! h
      exact h0 (hzero x h)
    refine Finset.sum_pos' (fun j _ => ?_) ⟨i, Finset.mem_univ _, ?_⟩
    · by_cases hj : 0 ≤ μ j
      · rw [hx j hj]; simp
      · rw [← neg_mul]
        exact mul_nonneg (neg_nonneg.2 (not_le.1 hj).le) (mul_self_nonneg _)
    · have : μ i < 0 := not_le.1 fun h => hi (hx i h)
      rw [← neg_mul]
      exact mul_pos (neg_pos.2 this) (mul_self_pos.2 hi)

end HSP
