import HilbertSmith.Interface.ChartReduction
import HilbertSmith.Interface.Collapse

/-!
# Lemma 5.6: finite quotient sheets

OpenAI's Lemma 5.6 (statement 05:386-407, proof 05:409-434): for a faithful action and every
`j ≥ 1` there are a nonempty open `V ⊆ Y ∖ {y∞}` and a locally constant `β` on `q⁻¹(V)`, with
values `ζ^i`, such that `β(g + w) = ζ^{ḡ} β(w)` (5.4). This file proves the route's input
`HilbertSmith.Interface.SheetsInput`, along OpenAI's proof:

* `exists_stabilizer_le` (05:410-413): some `x ∈ W` has stabilizer inside `H = p^j ℤ_[p]`;
  otherwise every stabilizer, a closed subgroup (`HilbertSmith.closed_eq_dvd_pow`), contains
  `p^{j−1} ℤ_[p]`, against faithfulness.
* `exists_sheet_nhds` (05:417-421): an `H`-invariant open `N ∋ x` whose translates by elements
  outside `H` are disjoint from it. OpenAI separates the finitely many points `τ^i z` of
  `Z = W/H` and intersects; here the same is done upstairs in `W`, with the compact set
  `ℤ_[p] ∖ H` and the tube lemma, and `N` is the `H`-saturation of a small open set.
* `sheetsInput` (05:421-434): `V = q(N)`; `q⁻¹(V)` is the disjoint union of the open sheets
  `g + N`, one for each class of `g` modulo `H`, and `β = χ_j(g)` on the sheet `g + N`.

The finite quotient `W/(p^j G) → W/G` and its homeomorphic sheets, which OpenAI also states, are
not needed: the route uses only `V` and `β` (`HilbertSmith.Interface.SheetMultiplier`).
Deicyde's `HilbertSmith/QuotientSheets.lean` builds the sheets for a finite group acting on `Z`;
working in `W` avoids constructing `Z`.
-/

namespace HilbertSmith.Interface

open Topology Set Filter OnePoint Pointwise

/-! ### The characters `χ_j` -/

section Characters

variable {p : ℕ} [Fact p.Prime]

/-- `χ_j` is a character: `χ_j(g + h) = χ_j(g) χ_j(h)`. -/
theorem χ_add (j : ℕ) (g h : ℤ_[p]) : χ p j (g + h) = χ p j g * χ p j h := by
  simp only [χ, map_add]
  rw [ZMod.val_add, ← pow_add]
  conv_rhs => rw [← Nat.mod_add_div ((PadicInt.toZModPow j g).val +
    (PadicInt.toZModPow j h).val) (p ^ j)]
  rw [pow_add, pow_mul, ζ_pow_pow, one_pow, mul_one]

/-- `χ_j` is constant on the cosets of `H_j = p^j ℤ_[p]`. -/
theorem χ_eq_of_sub_mem {j : ℕ} {g h : ℤ_[p]} (hgh : g - h ∈ padicSubgroup p j) :
    χ p j g = χ p j h := by
  have hker : g - h ∈ RingHom.ker (PadicInt.toZModPow (p := p) j) := by
    rw [PadicInt.ker_toZModPow]
    exact hgh
  rw [RingHom.sub_mem_ker_iff] at hker
  simp only [χ, hker]

/-- `|χ_j(g)| = 1`. -/
theorem norm_χ (j : ℕ) (g : ℤ_[p]) : ‖χ p j g‖ = 1 := by
  have h : p ^ j ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  rw [χ, norm_pow, ζ, (Complex.isPrimitiveRoot_exp (p ^ j) h).norm'_eq_one h, one_pow]

end Characters

namespace LocalAction

variable {p : ℕ} [Fact p.Prime] {k : ℕ} (A : LocalAction p k)

/-- **A point with small stabilizer** (05:410-413): for a faithful action and `j ≥ 1`, some
`x ∈ W` is fixed only by elements of `H_j = p^j ℤ_[p]`. Otherwise every stabilizer is a nonzero
closed subgroup not inside `H_j`, hence `p^i ℤ_[p]` with `i < j`, and `p^{j−1}` fixes every
point. -/
theorem exists_stabilizer_le (hfaith : A.Faithful) {j : ℕ} (hj : 1 ≤ j) :
    ∃ x : A.W, ∀ g : ℤ_[p], g +ᵥ x = x → g ∈ padicSubgroup p j := by
  by_contra! hall
  have hfix : ∀ x : A.W, (p : ℤ_[p]) ^ (j - 1) +ᵥ x = x := by
    intro x
    obtain ⟨g, hgx, hgH⟩ := hall x
    have hclosed : IsClosed ((AddAction.stabilizer ℤ_[p] x : AddSubgroup ℤ_[p]) : Set ℤ_[p]) :=
      isClosed_eq (continuous_id.vadd continuous_const) continuous_const
    have hne : AddAction.stabilizer ℤ_[p] x ≠ ⊥ := by
      intro hbot
      have hg : g ∈ AddAction.stabilizer ℤ_[p] x := hgx
      rw [hbot, AddSubgroup.mem_bot] at hg
      exact hgH (hg ▸ zero_mem _)
    obtain ⟨i, hi⟩ := closed_eq_dvd_pow p hclosed hne
    have hij : i ≤ j - 1 := by
      by_contra! hij
      exact hgH (mem_padicSubgroup.2 ((pow_dvd_pow _ (by omega)).trans ((hi g).1 hgx)))
    exact (hi _).2 (pow_dvd_pow _ hij)
  refine padic_pow_ne_zero (p := p) (j - 1) (hfaith.eq_of_vadd_eq_vadd fun x => ?_)
  rw [hfix x, zero_vadd]

/-- **Disjoint sheets around `x`** (05:417-421): if `x` is fixed only by elements of `H_j`, there
is an `H_j`-invariant open `N ∋ x` such that `g + N` is disjoint from `N` for every `g ∉ H_j`.
By the tube lemma on the compact set `ℤ_[p] ∖ H_j`, some open `N₀ ∋ x` satisfies
`g + y ≠ y'` for `g ∉ H_j` and `y, y' ∈ N₀`; then `N = H_j + N₀`. The invariance matches
OpenAI's picture of one sheet per class of `ℤ_[p]/H_j`; `sheetsInput` uses only the
disjointness. -/
theorem exists_sheet_nhds {j : ℕ} {x : A.W}
    (hx : ∀ g : ℤ_[p], g +ᵥ x = x → g ∈ padicSubgroup p j) :
    ∃ N : Set A.W, IsOpen N ∧ x ∈ N ∧ (∀ g ∈ padicSubgroup p j, ∀ y ∈ N, g +ᵥ y ∈ N) ∧
      ∀ g ∉ padicSubgroup p j, ∀ y ∈ N, ∀ y' ∈ N, g +ᵥ y ≠ y' := by
  have hC : IsCompact (padicSubgroup p j : Set ℤ_[p])ᶜ :=
    (isOpen_padicSubgroup j).isClosed_compl.isCompact
  have hn : IsOpen {q : ℤ_[p] × (A.W × A.W) | q.1 +ᵥ q.2.1 ≠ q.2.2} :=
    isOpen_ne_fun
      (continuous_vadd.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd)))
      (continuous_snd.comp continuous_snd)
  obtain ⟨u, v, -, hv, hCu, hxv, huv⟩ := generalized_tube_lemma hC isCompact_singleton hn (by
    rintro ⟨g, y, y'⟩ ⟨hg, hy⟩
    rw [mem_singleton_iff, Prod.mk.injEq] at hy
    obtain ⟨rfl, rfl⟩ := hy
    exact fun h => hg (hx g h))
  obtain ⟨a, b, ha, hb, hxa, hxb, hab⟩ := isOpen_prod_iff.1 hv x x (hxv rfl)
  -- `N₀ = a ∩ b`: for `g ∉ H_j` and `y, y' ∈ N₀`, `g + y ≠ y'`.
  have hN₀ : ∀ g ∉ padicSubgroup p j, ∀ y ∈ a ∩ b, ∀ y' ∈ a ∩ b, g +ᵥ y ≠ y' :=
    fun g hg y hy y' hy' => huv (mk_mem_prod (hCu hg) (hab (mk_mem_prod hy.1 hy'.2)))
  refine ⟨saturation p j (a ∩ b), isOpen_saturation j (ha.inter hb),
    subset_saturation j _ ⟨hxa, hxb⟩, fun g hg y hy => vadd_mem_saturation hg hy, ?_⟩
  intro g hg y hy y' hy' hyy
  obtain ⟨h, hh, y₀, hy₀, rfl⟩ := mem_saturation.1 hy
  obtain ⟨h', hh', y₀', hy₀', rfl⟩ := mem_saturation.1 hy'
  -- `g + h - h' ∉ H_j` moves `y₀ ∈ N₀` to `y₀' ∈ N₀`.
  refine hN₀ (-h' + (g + h)) (fun hmem => hg ?_) y₀ hy₀ y₀' hy₀' ?_
  · have := add_mem (add_mem hh' hmem) (neg_mem hh)
    rwa [add_neg_cancel_left, add_neg_cancel_right] at this
  · rw [add_vadd, add_vadd, hyy, neg_vadd_vadd]

end LocalAction

/-- **Lemma 5.6** (finite quotient sheets; 05:386-434) for every faithful local action: the
route's input `SheetsInput`. Take the point `x` of `LocalAction.exists_stabilizer_le` and the open
set `N` of `LocalAction.exists_sheet_nhds`; then `V = q(N)` and `β = χ_j(g)` on the sheet
`g + N`. -/
theorem sheetsInput : SheetsInput := by
  intro p _ k A hfaith j hj
  have := A.continuousVAdd_onePoint
  obtain ⟨x, hx⟩ := A.exists_stabilizer_le hfaith hj
  obtain ⟨N, hNo, hxN, -, hdisj⟩ := A.exists_sheet_nhds hx
  set V : Set A.Y := A.q '' (((↑) : A.W → OnePoint A.W) '' N)
  -- The points over `V` are the translates of `N`.
  have hmemV : ∀ w : OnePoint A.W, w ∈ A.q ⁻¹' V ↔ ∃ g : ℤ_[p], ∃ y ∈ N, w = ↑(g +ᵥ y) := by
    intro w
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, hq⟩
      obtain ⟨g, hg⟩ := AddAction.mem_orbit_iff.1
        (AddAction.orbitRel_apply.1 (Quotient.exact hq.symm))
      exact ⟨g, y, hy, by rw [← hg, LocalAction.vadd_coe]⟩
    · rintro ⟨g, y, hy, rfl⟩
      refine ⟨_, ⟨y, hy, rfl⟩, Quotient.sound ?_⟩
      exact AddAction.orbitRel_apply.2 (AddAction.mem_orbit_iff.2 ⟨-g, by
        rw [LocalAction.vadd_coe, neg_vadd_vadd]⟩)
  -- Two translates of `N` meet only if the translations agree modulo `H_j`.
  have hsame : ∀ g g' : ℤ_[p], ∀ y ∈ N, ∀ y' ∈ N, g +ᵥ y = g' +ᵥ y' → χ p j g = χ p j g' := by
    intro g g' y hy y' hy' h
    refine χ_eq_of_sub_mem ?_
    by_contra hg
    refine hdisj (-g' + g) (fun hmem => hg ?_) y hy y' hy' ?_
    · rwa [sub_eq_add_neg, add_comm]
    · rw [add_vadd, h, neg_vadd_vadd]
  classical
  let β : OnePoint A.W → ℂ := fun w =>
    if h : ∃ g : ℤ_[p], ∃ y ∈ N, w = ↑(g +ᵥ y) then χ p j h.choose else 0
  have hβ : ∀ g : ℤ_[p], ∀ y ∈ N, β ↑(g +ᵥ y) = χ p j g := by
    intro g y hy
    have h : ∃ g' : ℤ_[p], ∃ y' ∈ N, (↑(g +ᵥ y) : OnePoint A.W) = ↑(g' +ᵥ y') := ⟨g, y, hy, rfl⟩
    simp only [β, h, ↓reduceDIte]
    obtain ⟨y', hy', heq⟩ := h.choose_spec
    exact hsame _ _ y' hy' y hy (OnePoint.coe_injective heq).symm
  have hq : IsOpenQuotientMap (Quotient.mk (AddAction.orbitRel ℤ_[p] (OnePoint A.W))) :=
    AddAction.isOpenQuotientMap_quotientMk
  refine ⟨V, ⟨hq.isOpenMap _ (OnePoint.isOpenMap_coe _ hNo), ⟨_, ⟨_, ⟨x, hxN, rfl⟩, rfl⟩⟩,
    fun hinf => ?_, β, ?_, ?_, ?_⟩⟩
  · obtain ⟨g, y, -, h⟩ := (hmemV ∞).1 hinf
    exact OnePoint.infty_ne_coe _ h
  · -- `β` is constant, `χ_j(g)`, on the open sheet `g + N`.
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun w => ?_
    obtain ⟨g, y, hy, hw⟩ := (hmemV w.1).1 w.2
    have hS : IsOpen (((↑) : A.W → OnePoint A.W) '' (g +ᵥ N)) :=
      OnePoint.isOpenMap_coe _ (hNo.vadd g)
    have hwS : w.1 ∈ ((↑) : A.W → OnePoint A.W) '' (g +ᵥ N) :=
      ⟨g +ᵥ y, vadd_mem_vadd_set hy, hw.symm⟩
    filter_upwards [(hS.preimage continuous_subtype_val).mem_nhds hwS] with z hz
    obtain ⟨_, ⟨y', hy', rfl⟩, hz⟩ := hz
    simp only [Set.domRestrict_apply]
    rw [← hz, hw, hβ g y' hy', hβ g y hy]
  · intro w hw
    obtain ⟨g, y, hy, rfl⟩ := (hmemV w).1 hw
    rw [hβ g y hy, norm_χ]
  · intro g' w hw
    obtain ⟨g, y, hy, rfl⟩ := (hmemV w).1 hw
    rw [LocalAction.vadd_coe, ← add_vadd, hβ _ y hy, hβ g y hy, χ_add]

end HilbertSmith.Interface
