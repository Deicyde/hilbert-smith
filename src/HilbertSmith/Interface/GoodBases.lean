import HilbertSmith.Interface.LocalInputs

/-!
# Good neighbourhood bases on `S^d` and on `C_d`

§6 needs a basis of contractible open neighbourhoods at the base point `b_t` of a test
(06:101-107): on `S^d` for tests into the sphere, and on the close-pair test `C_d` (06:359-366).
OpenAI gets the second from `C_d` being a smooth manifold with boundary; the TeX does not state
the first. This file proves both, the route's inputs `SphereBasis` and `ClosePairBasis`, with
explicit contractions instead of charts.

* **Caps.** On the unit sphere, a cap `{x | c < ⟨x, a⟩}` with `0 ≤ c` is closed under the
  normalized straight path `nlerp x y t = ((1 − t) x + t y) / ‖(1 − t) x + t y‖`: the inner
  product with `a` of the unnormalized point is a convex combination, above `c ≥ 0`, and
  normalizing a vector of norm at most `1` only increases it. So a cap contracts onto any of its
  points. Caps around `a` with `c` near `1` are a basis at `a` (`sphereBasis`).
* **Boxes in `C_d`.** At `(a₀, a₁) ∈ C_d`, the neighbourhoods are the pairs in `C_d` with
  `x₀` in a cap at `a₀` and `x₁` in a cap at `a₁`. Choose `u` in the cap at `a₁` with
  `⟨a₀, u⟩ > 0`, and the cap at `a₀` so small that `⟨x₀, u⟩ > 0` on it. Then `(x₀, x₁)` moves to
  `(x₀, u)` along `nlerp x₁ u`, and `(x₀, u)` to `(a₀, u)` along `nlerp x₀ a₀`, and the inner
  product of the two coordinates stays nonnegative throughout, so the path stays in `C_d`
  (`closePairBasis`). This works at boundary points (`⟨a₀, a₁⟩ = 0`) as well as interior ones.
-/

namespace HilbertSmith.Interface

open Topology Set Metric unitInterval

noncomputable section

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin (d + 1))

/-! ### The normalized straight path -/

/-- The point at time `t` of the normalized straight path from `x` to `y`. -/
def nlerp (x y : E) (t : ℝ) : E :=
  ‖(1 - t) • x + t • y‖⁻¹ • ((1 - t) • x + t • y)

theorem nlerp_zero {x : E} (hx : ‖x‖ = 1) (y : E) : nlerp x y 0 = x := by
  simp [nlerp, hx]

theorem nlerp_one (x : E) {y : E} (hy : ‖y‖ = 1) : nlerp x y 1 = y := by
  simp [nlerp, hy]

theorem norm_nlerp {x y : E} {t : ℝ} (h : (1 - t) • x + t • y ≠ 0) : ‖nlerp x y t‖ = 1 := by
  rw [nlerp, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 h)]

theorem inner_nlerp (x y b : E) (t : ℝ) :
    inner ℝ (nlerp x y t) b =
      ‖(1 - t) • x + t • y‖⁻¹ * ((1 - t) * inner ℝ x b + t * inner ℝ y b) := by
  rw [nlerp, real_inner_smul_left, inner_add_left, real_inner_smul_left, real_inner_smul_left]

/-- Normalizing keeps the sign of an inner product. -/
theorem inner_nlerp_nonneg {x y b : E} {t : ℝ}
    (h : 0 ≤ (1 - t) * inner ℝ x b + t * inner ℝ y b) : 0 ≤ inner ℝ (nlerp x y t) b := by
  rw [inner_nlerp]
  exact mul_nonneg (inv_nonneg.2 (norm_nonneg _)) h

/-- On the segment, nonnegative inner products with `b` stay nonnegative after normalizing. -/
theorem inner_nlerp_nonneg_of {x y b : E} {t : ℝ} (ht : t ∈ I) (hx : 0 ≤ inner ℝ x b)
    (hy : 0 ≤ inner ℝ y b) : 0 ≤ inner ℝ (nlerp x y t) b :=
  inner_nlerp_nonneg (add_nonneg (mul_nonneg (by linarith [ht.2]) hx) (mul_nonneg ht.1 hy))

/-- For unit vectors and `t ∈ [0, 1]`, if the convex combination of the inner products with `b`
is positive, the unnormalized point is nonzero and normalizing only increases the inner product. -/
theorem le_inner_nlerp {x y b : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) {t : ℝ} (ht : t ∈ I)
    (h : 0 < (1 - t) * inner ℝ x b + t * inner ℝ y b) :
    (1 - t) • x + t • y ≠ 0 ∧
      (1 - t) * inner ℝ x b + t * inner ℝ y b ≤ inner ℝ (nlerp x y t) b := by
  obtain ⟨ht0, ht1⟩ := ht
  have hv : (1 - t) • x + t • y ≠ 0 := by
    intro hv
    have : inner ℝ ((1 - t) • x + t • y) b = 0 := by rw [hv, inner_zero_left]
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left] at this
    linarith
  refine ⟨hv, ?_⟩
  have hle : ‖(1 - t) • x + t • y‖ ≤ 1 := by
    calc ‖(1 - t) • x + t • y‖ ≤ ‖(1 - t) • x‖ + ‖t • y‖ := norm_add_le _ _
      _ = (1 - t) + t := by
          rw [norm_smul, norm_smul, hx, hy, Real.norm_of_nonneg (by linarith),
            Real.norm_of_nonneg ht0, mul_one, mul_one]
      _ = 1 := by ring
  have hpos : 0 < ‖(1 - t) • x + t • y‖ := norm_pos_iff.2 hv
  rw [inner_nlerp]
  exact le_mul_of_one_le_left h.le (one_le_inv₀ hpos |>.2 hle)

/-- The normalized straight path is continuous wherever the unnormalized point is nonzero. -/
theorem Continuous.nlerp {X : Type*} [TopologicalSpace X] {f g : X → E} {τ : X → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hτ : Continuous τ)
    (h : ∀ q, (1 - τ q) • f q + τ q • g q ≠ 0) :
    Continuous fun q => nlerp (f q) (g q) (τ q) := by
  have hv : Continuous fun q => (1 - τ q) • f q + τ q • g q :=
    ((continuous_const.sub hτ).smul hf).add (hτ.smul hg)
  exact ((continuous_norm.comp hv).inv₀ fun q => norm_ne_zero_iff.2 (h q)).smul hv

/-! ### Caps -/

/-- The cap `{x ∈ S^d | c < ⟨x, a⟩}`. -/
def cap (a : Sphere d) (c : ℝ) : Set (Sphere d) :=
  {x | c < inner ℝ (x : E) a}

theorem isOpen_cap (a : Sphere d) (c : ℝ) : IsOpen (cap a c) :=
  isOpen_lt continuous_const (continuous_subtype_val.inner continuous_const)

theorem mem_cap_self (a : Sphere d) {c : ℝ} (hc : c < 1) : a ∈ cap a c := by
  change c < inner ℝ (a : E) a
  rw [real_inner_self_eq_norm_sq, a.2, one_pow]
  exact hc

/-- A cap with `0 ≤ c` is closed under the normalized straight path. -/
theorem nlerp_mem_cap {a : Sphere d} {c : ℝ} (hc : 0 ≤ c) {x y : Sphere d} (hx : x ∈ cap a c)
    (hy : y ∈ cap a c) {t : ℝ} (ht : t ∈ I) :
    (1 - t) • (x : E) + t • (y : E) ≠ 0 ∧ c < inner ℝ (nlerp (x : E) y t) a := by
  have hconv : c < (1 - t) * inner ℝ (x : E) a + t * inner ℝ (y : E) a := by
    obtain ⟨ht0, ht1⟩ := ht
    have hx' : c < inner ℝ (x : E) a := hx
    have hy' : c < inner ℝ (y : E) a := hy
    rcases eq_or_lt_of_le ht0 with rfl | ht0'
    · linarith
    · nlinarith
  obtain ⟨hv, hle⟩ := le_inner_nlerp x.2 y.2 ht (hc.trans_lt hconv)
  exact ⟨hv, hconv.trans_le hle⟩

/-- The point `nlerp x y t` of a cap, as a point of the cap. -/
def capPath {a : Sphere d} {c : ℝ} (hc : 0 ≤ c) (x y : cap a c) (t : I) : cap a c :=
  ⟨⟨nlerp (x : E) (y : Sphere d) t, norm_nlerp (nlerp_mem_cap hc x.2 y.2 t.2).1⟩,
    (nlerp_mem_cap hc x.2 y.2 t.2).2⟩

/-- **A cap with `0 ≤ c` is contractible**: it contracts onto any of its points along the
normalized straight paths. -/
theorem contractibleSpace_cap {a : Sphere d} {c : ℝ} (hc : 0 ≤ c) (z : cap a c) :
    ContractibleSpace (cap a c) := by
  refine (contractible_iff_id_nullhomotopic _).2 ⟨z, ⟨?_⟩⟩
  exact
    { toFun := fun q => capPath hc q.2 z q.1
      continuous_toFun := by
        refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
        exact Continuous.nlerp
          (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd))
          continuous_const (continuous_subtype_val.comp continuous_fst)
          fun q => (nlerp_mem_cap hc q.2.2 z.2 q.1.2).1
      map_zero_left := fun x => Subtype.ext <| Subtype.ext <| nlerp_zero x.1.2 _
      map_one_left := fun x => Subtype.ext <| Subtype.ext <| nlerp_one _ z.1.2 }

/-- On unit vectors, `c < ⟨x, a⟩` with `c = 1 − ε²/2` puts `x` within `ε` of `a`. -/
theorem dist_lt_of_mem_cap {a x : Sphere d} {ε : ℝ} (hε : 0 < ε)
    (hx : x ∈ cap a (1 - ε ^ 2 / 2)) : dist x a < ε := by
  have hx' : 1 - ε ^ 2 / 2 < inner ℝ (x : E) a := hx
  have hsq : ‖(x : E) - a‖ ^ 2 < ε ^ 2 := by
    rw [norm_sub_sq_real, x.2, a.2]
    linarith
  rw [Subtype.dist_eq, dist_eq_norm]
  exact lt_of_pow_lt_pow_left₀ 2 hε.le hsq

/-- Small caps around `a` lie in any neighbourhood of `a`: for `N ∈ 𝓝 a` there is `c` with
`0 ≤ c < 1` and the cap `{c < ⟨x, a⟩}` inside `N`; and any larger `c' < 1` works too. -/
theorem exists_cap_subset {a : Sphere d} {N : Set (Sphere d)} (hN : N ∈ 𝓝 a) :
    ∃ c, 0 ≤ c ∧ c < 1 ∧ ∀ c', c ≤ c' → cap a c' ⊆ N := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hN
  set ε' := min ε 1
  have hε' : 0 < ε' := lt_min hε one_pos
  have hε'1 : ε' ≤ 1 := min_le_right _ _
  refine ⟨1 - ε' ^ 2 / 2, by nlinarith, by nlinarith, fun c' hc' x hx => hball ?_⟩
  exact (dist_lt_of_mem_cap hε' (lt_of_le_of_lt hc' hx)).trans_le (min_le_left _ _)

variable (d) in
/-- **Good neighbourhood bases on `S^d`**: small caps. -/
theorem sphereBasis : SphereBasis d := by
  intro a N hN
  obtain ⟨c, hc0, hc1, hcN⟩ := exists_cap_subset hN
  exact ⟨cap a c, hcN c le_rfl, mem_cap_self a hc1,
    ⟨isOpen_cap a c, ⟨a, mem_cap_self a hc1⟩, contractibleSpace_cap hc0 ⟨a, mem_cap_self a hc1⟩⟩⟩

/-! ### Boxes in `C_d` -/

/-- The box at `(a₀, a₁)` in `C_d`: pairs with `x₀` in the cap `{c₀ < ⟨x₀, a₀⟩}` and `x₁` in the
cap `{c₁ < ⟨x₁, a₁⟩}`. -/
def box (a₀ a₁ : Sphere d) (c₀ c₁ : ℝ) : Set (ClosePair d) :=
  {z | z.1.1 ∈ cap a₀ c₀ ∧ z.1.2 ∈ cap a₁ c₁}

theorem isOpen_box (a₀ a₁ : Sphere d) (c₀ c₁ : ℝ) : IsOpen (box a₀ a₁ c₀ c₁) :=
  ((isOpen_cap a₀ c₀).preimage (continuous_fst.comp continuous_subtype_val)).inter
    ((isOpen_cap a₁ c₁).preimage (continuous_snd.comp continuous_subtype_val))

/-- A point of a box from its two coordinates. -/
def box.mk {a₀ a₁ : Sphere d} {c₀ c₁ : ℝ} (x₀ : cap a₀ c₀) (x₁ : cap a₁ c₁)
    (h : 0 ≤ inner ℝ (x₀ : E) (x₁ : Sphere d)) : box a₀ a₁ c₀ c₁ :=
  ⟨⟨(x₀, x₁), h⟩, x₀.2, x₁.2⟩

/-- The first coordinate of a point of a box, in its cap. -/
def box.fst {a₀ a₁ : Sphere d} {c₀ c₁ : ℝ} (z : box a₀ a₁ c₀ c₁) : cap a₀ c₀ := ⟨z.1.1.1, z.2.1⟩

/-- The second coordinate of a point of a box, in its cap. -/
def box.snd {a₀ a₁ : Sphere d} {c₀ c₁ : ℝ} (z : box a₀ a₁ c₀ c₁) : cap a₁ c₁ := ⟨z.1.1.2, z.2.2⟩

theorem continuous_box_fst {a₀ a₁ : Sphere d} {c₀ c₁ : ℝ} :
    Continuous (box.fst : box a₀ a₁ c₀ c₁ → cap a₀ c₀) :=
  (continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _

theorem continuous_box_snd {a₀ a₁ : Sphere d} {c₀ c₁ : ℝ} :
    Continuous (box.snd : box a₀ a₁ c₀ c₁ → cap a₁ c₁) :=
  (continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _

theorem continuous_box_mk {X : Type*} [TopologicalSpace X] {a₀ a₁ : Sphere d} {c₀ c₁ : ℝ}
    {f : X → cap a₀ c₀} {g : X → cap a₁ c₁} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ q, 0 ≤ inner ℝ ((f q : Sphere d) : E) (g q : Sphere d)) :
    Continuous fun q => box.mk (f q) (g q) (h q) :=
  ((hf.subtype_val.prodMk hg.subtype_val).subtype_mk _).subtype_mk _

/-- **A box is contractible**, given `0 ≤ c₀, c₁`, a point `u` of the cap at `a₁` with
`⟨x₀, u⟩ > 0` on the cap at `a₀`, and `a₀` in its cap. First `(x₀, x₁)` moves to `(x₀, u)` along
`nlerp x₁ u`, then `(x₀, u)` to `(a₀, u)` along `nlerp x₀ a₀`; the inner product of the two
coordinates stays nonnegative, so both paths stay in `C_d`. -/
theorem contractibleSpace_box {a₀ a₁ : Sphere d} {c₀ c₁ : ℝ} (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁)
    (ha₀ : a₀ ∈ cap a₀ c₀) (u : cap a₁ c₁)
    (hu : ∀ x ∈ cap a₀ c₀, 0 < inner ℝ (x : E) (u : Sphere d)) :
    ContractibleSpace (box a₀ a₁ c₀ c₁) := by
  -- The middle map `(x₀, x₁) ↦ (x₀, u)`.
  let f : C(box a₀ a₁ c₀ c₁, box a₀ a₁ c₀ c₁) :=
    ⟨fun z => box.mk (box.fst z) u (hu _ (box.fst z).2).le,
      continuous_box_mk continuous_box_fst continuous_const _⟩
  have hA : (ContinuousMap.id _).Homotopic f := ⟨
    { toFun := fun q => box.mk (box.fst q.2) (capPath hc₁ (box.snd q.2) u q.1) (by
        change 0 ≤ inner ℝ (((box.fst q.2 : Sphere d) : E))
          (nlerp ((box.snd q.2 : Sphere d) : E) (u : Sphere d) q.1)
        rw [real_inner_comm]
        refine inner_nlerp_nonneg_of q.1.2 ?_ ?_
        · rw [real_inner_comm]; exact q.2.1.2
        · rw [real_inner_comm]; exact (hu _ (box.fst q.2).2).le)
      continuous_toFun := by
        refine continuous_box_mk (continuous_box_fst.comp continuous_snd)
          (Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _) _
        exact Continuous.nlerp
          (continuous_subtype_val.comp (continuous_subtype_val.comp
            (continuous_box_snd.comp continuous_snd)))
          continuous_const (continuous_subtype_val.comp continuous_fst)
          fun q => (nlerp_mem_cap hc₁ (box.snd q.2).2 u.2 q.1.2).1
      map_zero_left := fun z => Subtype.ext <| Subtype.ext <| Prod.ext rfl <|
        Subtype.ext <| nlerp_zero z.1.1.2.2 _
      map_one_left := fun z => Subtype.ext <| Subtype.ext <| Prod.ext rfl <|
        Subtype.ext <| nlerp_one _ u.1.2 }⟩
  have hB : f.Homotopic (ContinuousMap.const _ (box.mk ⟨a₀, ha₀⟩ u (hu a₀ ha₀).le)) := ⟨
    { toFun := fun q => box.mk (capPath hc₀ (box.fst q.2) ⟨a₀, ha₀⟩ q.1) u (by
        change 0 ≤ inner ℝ (nlerp ((box.fst q.2 : Sphere d) : E) a₀ q.1) ((u : Sphere d) : E)
        exact inner_nlerp_nonneg_of q.1.2 (hu _ (box.fst q.2).2).le (hu a₀ ha₀).le)
      continuous_toFun := by
        refine continuous_box_mk (Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _)
          continuous_const _
        exact Continuous.nlerp
          (continuous_subtype_val.comp (continuous_subtype_val.comp
            (continuous_box_fst.comp continuous_snd)))
          continuous_const (continuous_subtype_val.comp continuous_fst)
          fun q => (nlerp_mem_cap hc₀ (box.fst q.2).2 ha₀ q.1.2).1
      map_zero_left := fun z => Subtype.ext <| Subtype.ext <| Prod.ext
        (Subtype.ext <| nlerp_zero z.1.1.1.2 _) rfl
      map_one_left := fun z => Subtype.ext <| Subtype.ext <| Prod.ext
        (Subtype.ext <| nlerp_one _ a₀.2) rfl }⟩
  exact (contractible_iff_id_nullhomotopic _).2 ⟨_, hA.trans hB⟩

variable (d) in
/-- **Good neighbourhood bases on `C_d`**: small boxes (06:359-366). Given a neighbourhood of
`(a₀, a₁)`, take the cap at `a₁` with `c₁` near `1`, the point `u = nlerp a₁ a₀ s` of it with
`s = (1 − c₁)/2`, which has `⟨a₀, u⟩ > 0`, and a cap at `a₀` small enough for `⟨x₀, u⟩ > 0`. -/
theorem closePairBasis : ClosePairBasis d := by
  rintro ⟨⟨a₀, a₁⟩, h01⟩ N hN
  have h01' : 0 ≤ inner ℝ (a₀ : E) (a₁ : E) := h01
  -- `N` contains a product of neighbourhoods of `a₀` and `a₁`, intersected with `C_d`.
  rw [nhds_subtype_eq_comap, Filter.mem_comap] at hN
  obtain ⟨M, hM, hMN⟩ := hN
  rw [nhds_prod_eq, Filter.mem_prod_iff] at hM
  obtain ⟨N₀, hN₀, N₁, hN₁, hprod⟩ := hM
  obtain ⟨c₁, hc₁0, hc₁1, hc₁N⟩ := exists_cap_subset hN₁
  -- The point `u`.
  set s : ℝ := (1 - c₁) / 2
  have hs : s ∈ I := ⟨by simp only [s]; linarith, by simp only [s]; linarith⟩
  have hs0 : 0 < s := by simp only [s]; linarith
  have hs1 : s < 1 := by simp only [s]; linarith
  have hsh : 0 ≤ s * inner ℝ (a₀ : E) (a₁ : E) := mul_nonneg hs.1 h01'
  have hsh' : 0 ≤ (1 - s) * inner ℝ (a₀ : E) (a₁ : E) := mul_nonneg (by linarith) h01'
  have hsa₁ : 0 < (1 - s) * inner ℝ (a₁ : E) (a₁ : E) + s * inner ℝ (a₀ : E) (a₁ : E) := by
    rw [real_inner_self_eq_norm_sq, a₁.2, one_pow]
    linarith
  obtain ⟨hv, hua₁⟩ := le_inner_nlerp a₁.2 a₀.2 hs hsa₁
  set u₀ : Sphere d := ⟨nlerp (a₁ : E) a₀ s, norm_nlerp hv⟩
  have hu₀ : u₀ ∈ cap a₁ c₁ := by
    change c₁ < inner ℝ (nlerp (a₁ : E) a₀ s) a₁
    refine lt_of_lt_of_le ?_ hua₁
    rw [real_inner_self_eq_norm_sq, a₁.2, one_pow]
    have : c₁ < 1 - s := by simp only [s]; linarith
    linarith
  have hpos : 0 < inner ℝ (a₀ : E) (u₀ : E) := by
    rw [real_inner_comm]
    change 0 < inner ℝ (nlerp (a₁ : E) a₀ s) a₀
    refine lt_of_lt_of_le ?_ (le_inner_nlerp a₁.2 a₀.2 hs ?_).2
    · rw [real_inner_comm, real_inner_self_eq_norm_sq, a₀.2, one_pow]
      linarith
    · rw [real_inner_comm, real_inner_self_eq_norm_sq, a₀.2, one_pow]
      linarith
  -- The cap at `a₀`: inside `N₀`, and with `⟨x₀, u⟩ > 0`.
  have hU : {x : Sphere d | 0 < inner ℝ (x : E) (u₀ : E)} ∈ 𝓝 a₀ :=
    (isOpen_lt continuous_const (continuous_subtype_val.inner continuous_const)).mem_nhds hpos
  obtain ⟨c₀, hc₀0, hc₀1, hc₀N⟩ := exists_cap_subset (Filter.inter_mem hN₀ hU)
  have ha₀ : a₀ ∈ cap a₀ c₀ := mem_cap_self a₀ hc₀1
  refine ⟨box a₀ a₁ c₀ c₁, fun z hz => hMN ?_, ⟨mem_cap_self a₀ hc₀1, mem_cap_self a₁ hc₁1⟩,
    ⟨isOpen_box _ _ _ _, ⟨⟨(a₀, a₁), h01⟩, mem_cap_self a₀ hc₀1, mem_cap_self a₁ hc₁1⟩,
      contractibleSpace_box hc₀0 hc₁0 ha₀ ⟨u₀, hu₀⟩ fun x hx => (hc₀N c₀ le_rfl hx).2⟩⟩
  exact hprod ⟨(hc₀N c₀ le_rfl hz.1).1, hc₁N c₁ le_rfl hz.2⟩

end

end HilbertSmith.Interface
