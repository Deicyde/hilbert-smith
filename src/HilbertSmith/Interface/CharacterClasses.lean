import HilbertSmith.Interface.Invariant

/-!
# Character classes

Definition 6.3 and Propositions 6.4, 6.5 and 6.7 of OpenAI's preprint, proved from the interface
`OrbitCharacterTheory` with no sheaves: these are the formal steps of §6.

* `OrbitCharacterTheory.z`: the character classes `zᵢ(t) ∈ E_d(X)` of Definition 6.3, defined by
  `ℓ_U(zᵢ(t)) = [A_t, α_t] + [A_t, α_t(2eᵢ − 1)]` for a good neighbourhood `U` of `b_t`;
  `OrbitCharacterTheory.z_eq_zAt`: the choice of `U` does not matter (06:245-250).
* `OrbitCharacterTheory.sum_z`: Proposition 6.4, `∑ᵢ zᵢ(t) = 2[A_t, α_t] = 4 (f_t)_* u_d`.
* `OrbitCharacterTheory.map_z`: Proposition 6.5, `g_* zᵢ(t) = zᵢ(gt)`.
* `OrbitCharacterTheory.z_eq_of_sheet`: Proposition 6.7, the classes of a test concentrated on a
  sheet region are all equal.
-/

namespace HilbertSmith.Interface

open CategoryTheory Topology Set

noncomputable section

variable {d : ℕ} {δD : DegreeMaps d} {I : OAIInvariant d δD}
  {OP : ∀ {p : ℕ} [Fact p.Prime] {k : ℕ}, LocalAction p k → Prop}

namespace OrbitCharacterTheory

variable (Ch : OrbitCharacterTheory I OP) {p : ℕ} [Fact p.Prime] (A : LocalAction p d)
  (hOP : OP A) {X : Type} [TopologicalSpace X]

/-- The projectors are idempotent, from (6.6). -/
theorem proj_idem {t : C(A.Y, X)} {U : Set X} (h : Admissible I A t U) {m : ℕ}
    (κ : Λ p → Fin m) (i : Fin m) : Ch.proj A t U κ i ≫ Ch.proj A t U κ i = Ch.proj A t U κ i := by
  simpa using Ch.proj_mul A t U h κ i i

/-- The twisted test form `(A_t, α_t(2eᵢ − 1))` of Definition 6.3. -/
def twistForm (t : C(A.Y, X)) (U : Set X) (h : Admissible I A t U) {m : ℕ} (κ : Λ p → Fin m)
    (i : Fin m) : Form (I.dual X U) :=
  (Ch.form A t U).twist (Ch.proj A t U κ i) (Ch.proj_idem A h κ i) (Ch.proj_adj A hOP t U h κ i)

/-- `[A_t, α_t] + [A_t, α_t(2eᵢ − 1)] ∈ W_d(𝒬_U(X))`, the right side of (6.7). -/
def zQ (t : C(A.Y, X)) (U : Set X) (h : Admissible I A t U) {m : ℕ} (κ : Λ p → Fin m)
    (i : Fin m) : I.WQ X U :=
  (I.witt X U).cls (Ch.form A t U) + (I.witt X U).cls (Ch.twistForm A hOP t U h κ i)

/-- The class `zᵢ(t)` computed with the neighbourhood `U`: `ℓ_U⁻¹` of (6.7). -/
def zAt (t : C(A.Y, X)) (U : Set X) (h : Admissible I A t U) {m : ℕ} (κ : Λ p → Fin m)
    (i : Fin m) : I.E X :=
  (I.ℓ X U h.isTest h.good).symm (Ch.zQ A hOP t U h κ i)

open Classical in
/-- **The character classes** `zᵢ(t) ∈ E_d(X)` (Definition 6.3), for a test `t` admitting a good
neighbourhood of `b_t` (and `0` otherwise). By `z_eq_zAt` any good neighbourhood computes them. -/
def z (t : C(A.Y, X)) {m : ℕ} (κ : Λ p → Fin m) (i : Fin m) : I.E X :=
  if h : ∃ U, Admissible I A t U then Ch.zAt A hOP t h.choose h.choose_spec κ i else 0

/-- `ḡ_*` carries the classes (6.7) for `t` to those for `gt`: the identification of
`OrbitCharacterTheory.push`, applied to the form and to its twist. -/
theorem wmap_zQ {X' : Type} [TopologicalSpace X'] (t : C(A.Y, X)) (g : C(X, X')) (U : Set X)
    (U' : Set X') (hU : Admissible I A t U) (hU' : Admissible I A (g.comp t) U')
    (hg : MapsTo g U U') {m : ℕ} (κ : Λ p → Fin m) (i : Fin m) :
    I.wmap g U U' hg (Ch.zQ A hOP t U hU κ i) = Ch.zQ A hOP (g.comp t) U' hU' κ i := by
  obtain ⟨e, he⟩ := Ch.push A t g U U' hU hU' hg
  rw [zQ, zQ, map_add, I.wmap_cls, I.wmap_cls]
  congr 1
  · exact (I.witt X' U').cls_isometry e
  · exact (I.witt X' U').cls_isometry
      ((I.pushQ g U U' hg).mapFormTwist e _ _ _ _ (he κ i))

/-- `g_*` carries `zᵢ(t)` computed with `U` to `zᵢ(gt)` computed with `U'`, when `g(U) ⊆ U'`:
naturality of `ℓ` and `wmap_zQ`. -/
theorem map_zAt {X' : Type} [TopologicalSpace X'] (t : C(A.Y, X)) (g : C(X, X')) (U : Set X)
    (U' : Set X') (hU : Admissible I A t U) (hU' : Admissible I A (g.comp t) U')
    (hg : MapsTo g U U') {m : ℕ} (κ : Λ p → Fin m) (i : Fin m) :
    I.map g (Ch.zAt A hOP t U hU κ i) = Ch.zAt A hOP (g.comp t) U' hU' κ i := by
  apply (I.ℓ X' U' hU'.isTest hU'.good).injective
  rw [I.ℓ_natural g U U' hU.isTest hU'.isTest hU.good hU'.good hg, zAt, zAt,
    AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, Ch.wmap_zQ]

/-- A good neighbourhood of `b_t` inside any given neighbourhood, for an admissible test. -/
theorem exists_admissible_subset {t : C(A.Y, X)} (hX : I.IsTest X) [CompactSpace X]
    [T2Space X] (hb : HasGoodBasisAt (t A.yinf)) {N : Set X} (hN : N ∈ 𝓝 (t A.yinf)) :
    ∃ U ⊆ N, Admissible I A t U := by
  obtain ⟨U, hUN, hbU, hU⟩ := hb N hN
  exact ⟨U, hUN, ⟨hX, inferInstance, inferInstance, hb, hU, hbU⟩⟩

/-- **Definition 6.3 does not depend on `U`** (06:245-250): compare both choices with a good
neighbourhood inside their intersection, through the quotient functors (`map_zAt` for `g = id`). -/
theorem zAt_eq {t : C(A.Y, X)} {U₁ U₂ : Set X} (h₁ : Admissible I A t U₁)
    (h₂ : Admissible I A t U₂) {m : ℕ} (κ : Λ p → Fin m) (i : Fin m) :
    Ch.zAt A hOP t U₁ h₁ κ i = Ch.zAt A hOP t U₂ h₂ κ i := by
  have := h₁.compact
  have := h₁.t2
  have hN : U₁ ∩ U₂ ∈ 𝓝 (t A.yinf) :=
    Filter.inter_mem (h₁.good.isOpen.mem_nhds h₁.mem) (h₂.good.isOpen.mem_nhds h₂.mem)
  obtain ⟨U₀, hU₀, h₀⟩ := exists_admissible_subset A h₁.isTest h₁.basis hN
  have key : ∀ {U : Set X} (hU : Admissible I A t U), U₀ ⊆ U →
      Ch.zAt A hOP t U₀ h₀ κ i = Ch.zAt A hOP t U hU κ i := by
    intro U hU hsub
    have := Ch.map_zAt A hOP t (ContinuousMap.id X) U₀ U h₀ hU (fun x hx => hsub hx) κ i
    rwa [I.map_id X h₀.isTest] at this
  rw [← key h₁ (hU₀.trans inter_subset_left), key h₂ (hU₀.trans inter_subset_right)]

/-- Any admissible neighbourhood computes `zᵢ(t)`. -/
theorem z_eq_zAt {t : C(A.Y, X)} {U : Set X} (h : Admissible I A t U) {m : ℕ}
    (κ : Λ p → Fin m) (i : Fin m) : Ch.z A hOP t κ i = Ch.zAt A hOP t U h κ i := by
  have hex : ∃ U, Admissible I A t U := ⟨U, h⟩
  simp only [z, hex, ↓reduceDIte]
  exact Ch.zAt_eq A hOP _ _ κ i

/-- **Proposition 6.4** (sum of the character classes): for a compact test `t` with a good
neighbourhood basis at `b_t` and every finite partition of the characters,
`∑ᵢ zᵢ(t) = 2[A_t, α_t] = 4 (f_t)_* u_d`. The computation in `𝒬_U(X)` is
`WittClasses.sum_cls_twist`; the identity `[A_t, α_t] = 2 (f_t)_* u_d` is
`OrbitCharacterTheory.form_cls`. -/
theorem sum_z (t : C(A.Y, X)) (hX : I.IsTest X) [CompactSpace X] [T2Space X]
    (hb : HasGoodBasisAt (t A.yinf)) {m : ℕ} (κ : Λ p → Fin m) :
    ∑ i, Ch.z A hOP t κ i = 4 • I.map (t.comp A.qc) I.u := by
  obtain ⟨U, -, hU⟩ := exists_admissible_subset A hX hb Filter.univ_mem
  simp_rw [Ch.z_eq_zAt A hOP hU]
  apply (I.ℓ X U hU.isTest hU.good).injective
  have hsum := (I.witt X U).sum_cls_twist (Ch.form A t U) (Ch.proj A t U κ)
    (Ch.proj_idem A hU κ) (fun i j hij => by simpa [hij] using Ch.proj_mul A t U hU κ i j)
    (Ch.proj_sum A t U hU κ) (Ch.proj_adj A hOP t U hU κ)
  rw [map_sum]
  simp only [zAt, AddEquiv.apply_symm_apply, zQ, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin]
  rw [show (4 : ℕ) = 2 * 2 from rfl, mul_nsmul', map_nsmul, Ch.form_cls A t U hU]
  change m • _ + ∑ i, (I.witt X U).cls (Ch.twistForm A hOP t U hU κ i) = _
  unfold twistForm
  rw [hsum, ← natCast_zsmul, ← natCast_zsmul, ← add_smul]
  congr 1
  push_cast
  ring

/-- **Proposition 6.5** (covariance on compact tests): `g_* zᵢ(t) = zᵢ(gt)` for a continuous map
`g : X → X'` of compact tests with good neighbourhood bases at `b_t` and `g(b_t)`. Choose a good
`U' ∋ g(b_t)`, then a good `U ∋ b_t` with `g(U) ⊆ U'` (06:306-307), and apply `map_zAt`. -/
theorem map_z {X' : Type} [TopologicalSpace X'] (t : C(A.Y, X)) (g : C(X, X'))
    (hX : I.IsTest X) (hX' : I.IsTest X') [CompactSpace X] [CompactSpace X'] [T2Space X]
    [T2Space X'] (hb : HasGoodBasisAt (t A.yinf)) (hb' : HasGoodBasisAt (g (t A.yinf)))
    {m : ℕ} (κ : Λ p → Fin m) (i : Fin m) :
    I.map g (Ch.z A hOP t κ i) = Ch.z A hOP (g.comp t) κ i := by
  obtain ⟨U', -, hU'⟩ := exists_admissible_subset (t := g.comp t) A hX' hb' Filter.univ_mem
  obtain ⟨U, hUU', hU⟩ := exists_admissible_subset A hX hb
    (g.continuous.continuousAt.preimage_mem_nhds (hU'.good.isOpen.mem_nhds hU'.mem))
  rw [Ch.z_eq_zAt A hOP hU, Ch.z_eq_zAt A hOP hU']
  exact Ch.map_zAt A hOP t g U U' hU hU' (fun x hx => hUU' hx) κ i

/-- **Proposition 6.7** (equality for a concentrated test), one step: if `h` is constant off a
sheet region `V` of level `k` and `κ` is a cyclic partition, then `zᵢ(h) = z_{i−1}(h)`. The
isometry of `OrbitCharacterTheory.twist` identifies the twisted forms (06:437-442). -/
theorem z_eq_z_sub_one (k : ℕ) (V : Set A.Y) (hV : SheetMultiplier A k V) (h : C(A.Y, X))
    (hconst : ∀ y ∉ V, h y = h A.yinf) (hX : I.IsTest X) [CompactSpace X] [T2Space X]
    (hb : HasGoodBasisAt (h A.yinf)) (κ : Λ p → Fin (p ^ k)) (hκ : IsCyclicPartition p k κ)
    (i : Fin (p ^ k)) : Ch.z A hOP h κ i = Ch.z A hOP h κ (i - 1) := by
  obtain ⟨U, -, hU⟩ := exists_admissible_subset A hX hb Filter.univ_mem
  obtain ⟨σ, hσ⟩ := Ch.twist A k V hV h hconst U hU κ hκ
  rw [Ch.z_eq_zAt A hOP hU, Ch.z_eq_zAt A hOP hU, zAt, zAt, zQ, zQ]
  congr 2
  exact (I.witt X U).cls_isometry (Form.Isometry.twist σ _ _ _ _ (hσ i))

open Fin.NatCast in
/-- **Proposition 6.7** (equality for a concentrated test): all the classes `zᵢ(h)` are equal. -/
theorem z_eq_of_sheet (k : ℕ) (V : Set A.Y) (hV : SheetMultiplier A k V) (h : C(A.Y, X))
    (hconst : ∀ y ∉ V, h y = h A.yinf) (hX : I.IsTest X) [CompactSpace X] [T2Space X]
    (hb : HasGoodBasisAt (h A.yinf)) (κ : Λ p → Fin (p ^ k)) (hκ : IsCyclicPartition p k κ)
    (i j : Fin (p ^ k)) : Ch.z A hOP h κ i = Ch.z A hOP h κ j := by
  have step : ∀ i : Fin (p ^ k), Ch.z A hOP h κ (i + 1) = Ch.z A hOP h κ i := fun i => by
    simpa using Ch.z_eq_z_sub_one A hOP k V hV h hconst hX hb κ hκ (i + 1)
  have hzero : ∀ n : ℕ, Ch.z A hOP h κ (n : Fin (p ^ k)) = Ch.z A hOP h κ 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Nat.cast_succ, step, ih]
  rw [← Fin.cast_val_eq_self i, ← Fin.cast_val_eq_self j, hzero, hzero]

end OrbitCharacterTheory

end

end HilbertSmith.Interface
