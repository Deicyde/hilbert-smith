import HilbertSmith.Interface.CharacterClasses
import HilbertSmith.Interface.ChartReduction
import HilbertSmith.Interface.GoodBases
import HilbertSmith.Interface.Sheets
import HilbertSmith.Interface.ClosePair
import HilbertSmith.Interface.MoveTest
import HilbertSmith.Statements

/-!
# p-adic exclusion from OpenAI's interface

The end of OpenAI's proof, from the interface: Proposition 6.6, Theorem 6.8 (the contradiction
on the invariant chart), and the proof of Theorem 1.2 (p-adic exclusion).

* `OrbitCharacterTheory.z_homotopic`: Proposition 6.6, homotopic tests into `S^d` have equal
  character classes.
* `OrbitCharacterTheory.false_of_test`: Theorem 6.8, for a faithful orientation-preserving action
  on `W ⊆ ℝ^d` with an averaged test `a` that can be moved into every open region.
* `HilbertSmith.Interface.false_of_localAction`: the contradiction from a faithful action on a
  connected open subset of `ℝ^n`.
* `HilbertSmith.Interface.padicExclusion_of_oaiInterface_noSC`: Theorem 1.2 without second
  countability, from `OAIInterface`, `LocalInputs` and `NewmanInput` (through Proposition 5.1,
  `chartReductionNoSC`).
* `HilbertSmith.Interface.padicExclusion_of_oaiInterface`: Theorem 1.2 for second-countable
  manifolds, the analogue of HS_proof's `HSFormal.padicExclusion_of_inputs`.
-/

namespace HilbertSmith.Interface

open Topology Set

universe u

/-! ### Rational equality -/

namespace RatEq

variable {A : Type*} [AddCommGroup A] {x y z x' y' : A}

/-- Equal elements are rationally equal. -/
theorem of_eq (h : x = y) : RatEq x y := ⟨1, one_pos, by rw [h]⟩

/-- Rational equality is symmetric. -/
theorem symm (h : RatEq x y) : RatEq y x := by
  obtain ⟨ν, hν, h⟩ := h
  exact ⟨ν, hν, h.symm⟩

/-- Rational equality is transitive. -/
theorem trans (h₁ : RatEq x y) (h₂ : RatEq y z) : RatEq x z := by
  obtain ⟨ν, hν, h₁⟩ := h₁
  obtain ⟨μ, hμ, h₂⟩ := h₂
  refine ⟨μ * ν, Nat.mul_pos hμ hν, ?_⟩
  calc (μ * ν) • x = μ • ν • x := mul_smul _ _ _
    _ = ν • μ • y := by rw [h₁, smul_comm]
    _ = (μ * ν) • z := by rw [h₂, smul_comm, ← mul_smul]

/-- Rational equality is compatible with addition. -/
theorem add (h₁ : RatEq x y) (h₂ : RatEq x' y') : RatEq (x + x') (y + y') := by
  obtain ⟨ν, hν, h₁⟩ := h₁
  obtain ⟨μ, hμ, h₂⟩ := h₂
  refine ⟨μ * ν, Nat.mul_pos hμ hν, ?_⟩
  have e₁ : (μ * ν) • x = (μ * ν) • y := by rw [mul_smul, h₁, ← mul_smul]
  have e₂ : (μ * ν) • x' = (μ * ν) • y' := by rw [mul_comm, mul_smul, h₂, ← mul_smul]
  rw [smul_add, smul_add, e₁, e₂]

/-- Additive maps preserve rational equality. -/
theorem map {B : Type*} [AddCommGroup B] (f : A →+ B) (h : RatEq x y) :
    RatEq (f x) (f y) := by
  obtain ⟨ν, hν, h⟩ := h
  exact ⟨ν, hν, by rw [← map_nsmul, h, map_nsmul]⟩

/-- Rational equality is compatible with integer multiples. -/
theorem zsmul (n : ℤ) (h : RatEq x y) : RatEq (n • x) (n • y) := by
  obtain ⟨ν, hν, h⟩ := h
  exact ⟨ν, hν, by rw [smul_comm, h, smul_comm]⟩

/-- Rational equality is compatible with finite sums. -/
theorem sum {ι : Type*} (s : Finset ι) {f g : ι → A} (h : ∀ i ∈ s, RatEq (f i) (g i)) :
    RatEq (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact of_eq rfl
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/-- If no positive multiple of `u` vanishes, rationally equal integer multiples of `u` have equal
coefficients. -/
theorem int_eq {u : A} (hu : ∀ ν : ℕ, 0 < ν → ν • u ≠ 0) {a b : ℤ} (h : RatEq (a • u) (b • u)) :
    a = b := by
  obtain ⟨ν, hν, h⟩ := h
  by_contra hab
  have h0 : ((ν : ℤ) * (a - b)) • u = 0 := by
    rw [mul_smul, natCast_zsmul, sub_smul, smul_sub, h, sub_self]
  have hn : 0 < ((ν : ℤ) * (a - b)).natAbs := by
    rw [Int.natAbs_pos]
    exact mul_ne_zero (by exact_mod_cast hν.ne') (sub_ne_zero.mpr hab)
  apply hu _ hn
  rcases Int.natAbs_eq ((ν : ℤ) * (a - b)) with he | he
  · rw [← natCast_zsmul, ← he, h0]
  · rw [← natCast_zsmul, show (((ν : ℤ) * (a - b)).natAbs : ℤ) = -((ν : ℤ) * (a - b)) by omega,
      neg_smul, h0, neg_zero]

end RatEq

noncomputable section

variable {d : ℕ} {δD : DegreeMaps d} {I : OAIInvariant d δD}
  {OP : ∀ {p : ℕ} [Fact p.Prime] {k : ℕ}, LocalAction p k → Prop}

/-- The composite degree maps act on `ū_d` by `(s + 1)!`: Proposition 4.8 for each `D k`
(`OAIInvariant.mapD`) and functoriality. -/
theorem OAIInvariant.mapD_comp (I : OAIInvariant d δD) (s : ℕ) :
    RatEq (I.map (δD.comp s) I.u) (((s + 1).factorial : ℤ) • I.u) := by
  induction s with
  | zero =>
    exact RatEq.of_eq (by simp [DegreeMaps.comp, I.map_id _ I.isTest_sphere])
  | succ s ih =>
    rw [DegreeMaps.comp, I.map_comp I.isTest_sphere I.isTest_sphere I.isTest_sphere,
      AddMonoidHom.comp_apply]
    refine (ih.map (I.map (δD.D (s + 2)))).trans ?_
    rw [map_zsmul]
    refine ((I.mapD (s + 2) (by omega)).zsmul _).trans (RatEq.of_eq ?_)
    rw [smul_smul, Nat.factorial_succ (s + 1)]
    push_cast
    ring_nf

namespace OrbitCharacterTheory

variable (Ch : OrbitCharacterTheory I OP) {p : ℕ} [Fact p.Prime] (A : LocalAction p d)
  (hOP : OP A)

/-- **Proposition 6.6** (homotopy of character classes): homotopic tests `t₀ ≃ t₁ : Y → S^d` have
equal classes. Subdivide the homotopy so that consecutive stages form a test `Y → C_d`
(`ClosePair.eq_of_homotopic`); for such a test `s`, Proposition 6.5 along the projections and
Theorem 2.9 for `π₀ ≃ π₁` give `zᵢ(π₀ s) = π₀_* zᵢ(s) = π₁_* zᵢ(s) = zᵢ(π₁ s)` (06:384-389). -/
theorem z_homotopic (hS : SphereBasis d) (hCP : ClosePairBasis d) {t₀ t₁ : C(A.Y, Sphere d)}
    (h : t₀.Homotopic t₁) {m : ℕ} (κ : Λ p → Fin m) (i : Fin m) :
    Ch.z A hOP t₀ κ i = Ch.z A hOP t₁ κ i := by
  refine ClosePair.eq_of_homotopic (fun t => Ch.z A hOP t κ i) (fun s => ?_) h
  rw [← Ch.map_z A hOP s (ClosePair.π₀ d) I.isTest_closePair I.isTest_sphere (hCP _) (hS _),
    ← Ch.map_z A hOP s (ClosePair.π₁ d) I.isTest_closePair I.isTest_sphere (hCP _) (hS _),
    I.map_homotopic I.isTest_closePair I.isTest_sphere (ClosePair.homotopic_π d)]

include Ch hOP in
/-- **Theorem 6.8** (contradiction on the invariant chart), in the form its proof uses
(06:451-500). Given a faithful orientation-preserving local action on `W ⊆ ℝ^d` and a test
`a : Y → S^d` with `a ∘ q ∘ c ≃ id` that can be moved, after some `D_s`, into every open region
`V ⊆ Y ∖ {y∞}` (Proposition 5.8), we reach a contradiction. Choose `k` with `m = p^k > 4 L_d`, a
cyclic partition and a sheet region `V` (Lemma 5.6), and `h ≃ D_s a` constant off `V`. Then
`D_{s*} zᵢ(a) = zᵢ(D_s a) = zᵢ(h) = zⱼ(h) = D_{s*} zⱼ(a)`; since `D_{s*}` multiplies by
`(s + 1)! > 0` on the rational line, all `L_d zᵢ(a)` have the same rational coefficient `c`. The
sum is `∑ zᵢ(a) = 4 (aqc)_* u_d = 4 u_d`, so `m c = 4 L_d`, contradicting `0 < 4 L_d < m`. -/
theorem false_of_test (hS : SphereBasis d) (hCP : ClosePairBasis d) (hSh : SheetsInput)
    (hfaith : A.Faithful) (a : C(A.Y, Sphere d))
    (haqc : (a.comp A.qc).Homotopic (ContinuousMap.id _))
    (hmove : ∀ V : Set A.Y, IsOpen V → V.Nonempty → A.yinf ∉ V →
      ∃ (s : ℕ) (h : C(A.Y, Sphere d)), h.Homotopic ((δD.comp s).comp a) ∧
        ∀ y ∉ V, h y = h A.yinf) : False := by
  -- Fix the lattice and choose `k` with `m = p ^ k > 4 L_d`.
  have hp := (Fact.out : p.Prime)
  set k := 4 * I.L + 1 with hk
  have hm : 4 * I.L < p ^ k := lt_trans (by omega) (Nat.lt_pow_self hp.one_lt)
  obtain ⟨κ, hκ⟩ := exists_isCyclicPartition p k
  obtain ⟨V, hV⟩ := hSh A hfaith k (by omega)
  obtain ⟨s, h, hh, hconst⟩ := hmove V hV.isOpen hV.nonempty hV.yinf_notMem
  have hb : ∀ t : C(A.Y, Sphere d), HasGoodBasisAt (t A.yinf) := fun t => hS _
  -- `D_{s*} zᵢ(a)` does not depend on `i`.
  have hD : ∀ i j, I.map (δD.comp s) (Ch.z A hOP a κ i) = I.map (δD.comp s) (Ch.z A hOP a κ j) := by
    intro i j
    rw [Ch.map_z A hOP a _ I.isTest_sphere I.isTest_sphere (hS _) (hS _),
      Ch.map_z A hOP a _ I.isTest_sphere I.isTest_sphere (hS _) (hS _),
      ← Ch.z_homotopic A hOP hS hCP hh, ← Ch.z_homotopic A hOP hS hCP hh,
      Ch.z_eq_of_sheet A hOP k V hV h hconst I.isTest_sphere (hb h) κ hκ i j]
  -- The lattice: `L_d zᵢ(a) ≈ cᵢ u_d`, and all the `cᵢ` are equal.
  choose c hc using fun i => I.lattice (Ch.z A hOP a κ i)
  set s' : ℤ := ((s + 1).factorial : ℤ)
  have hs' : s' ≠ 0 := by positivity
  have hDc : ∀ i, RatEq (I.L • I.map (δD.comp s) (Ch.z A hOP a κ i)) ((c i * s') • I.u) := by
    intro i
    rw [← map_nsmul]
    refine ((hc i).map _).trans ?_
    rw [map_zsmul, mul_smul]
    exact (I.mapD_comp s).zsmul _
  have hcc : ∀ i, c i = c 0 := by
    intro i
    have := (hDc i).symm.trans (by rw [hD i 0]; exact hDc 0)
    exact mul_right_cancel₀ hs' (RatEq.int_eq I.u_nontorsion this)
  -- The sum: `∑ zᵢ(a) = 4 u_d`.
  have hsum : ∑ i, Ch.z A hOP a κ i = 4 • I.u := by
    rw [Ch.sum_z A hOP a I.isTest_sphere (hb a),
      I.map_homotopic I.isTest_sphere I.isTest_sphere haqc, I.map_id _ I.isTest_sphere,
      AddMonoidHom.id_apply]
  have hfinal : RatEq (((4 * I.L : ℕ) : ℤ) • I.u) (((p ^ k : ℕ) * c 0 : ℤ) • I.u) := by
    have h1 : RatEq (I.L • ∑ i, Ch.z A hOP a κ i) (∑ _i : Fin (p ^ k), c 0 • I.u) := by
      rw [Finset.smul_sum]
      exact RatEq.sum _ fun i _ => by rw [← hcc i]; exact hc i
    rw [hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin] at h1
    refine RatEq.trans (RatEq.of_eq ?_) (h1.trans (RatEq.of_eq ?_))
    · rw [smul_smul, natCast_zsmul, mul_comm]
    · rw [← natCast_zsmul, smul_smul]
  have := RatEq.int_eq I.u_nontorsion hfinal
  have hL := I.L_pos
  have hc0 : 0 < c 0 := by
    by_contra hneg
    replace hneg := not_lt.mp hneg
    have : ((p ^ k : ℕ) : ℤ) * c 0 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hneg
    omega
  have : ((p ^ k : ℕ) : ℤ) ≤ ((p ^ k : ℕ) : ℤ) * c 0 := le_mul_of_one_le_right (by positivity) hc0
  omega

end OrbitCharacterTheory

/-- **The contradiction from a faithful local action** (the proof of Theorem 1.2, 06:502-516,
after Proposition 5.1). Given a faithful action of `ℤ_[p]` on a connected open `O ⊆ ℝ^n`: an open
subgroup acts preserving orientation (`Orientation.exists_restrict`); stabilize to
`W = O × ℝ^{d−n}` with `d = 2n + 3`; Lemma 5.3 (`LocalInputs.averagedTest`) gives the test `a`
after a further open subgroup, with `a ∘ q` homotopic to a pinch, so (5.1) holds
(`aqc_homotopic_id`); the pinch transport (`pinchTransport`, through `hpinch_of`) and
Proposition 5.8 (`moveTest`) move it; and Theorem 6.8 (`false_of_test`) is the contradiction. -/
theorem false_of_localAction (O : OAIInterface) (T : LocalInputs O) {p : ℕ} [Fact p.Prime]
    {n : ℕ} (A₀ : LocalAction p n) (hconn₀ : IsConnected A₀.W) (hfaith₀ : A₀.Faithful) : False := by
  obtain ⟨j₁, hOP₁⟩ := T.orientation.exists_restrict A₀ hconn₀
  have hnd : n ≤ 2 * n + 3 := by omega
  set A₂ := (A₀.restrict j₁).stabilize (2 * n + 3) hnd
  have hOP₂ : O.OP A₂ := T.orientation.stabilize _ _ hnd hOP₁
  have hfaith₂ : A₂.Faithful :=
    LocalAction.stabilize_faithful _ _ _ (A₀.restrict_faithful j₁ hfaith₀)
  have hconn₂ : IsConnected A₂.W := LocalAction.stabilize_isConnected _ _ _ hconn₀
  obtain ⟨j₂, a, z, r, hr, hzr, haq⟩ := T.averagedTest n A₂ hconn₂.nonempty
  have hpinch := hpinch_of _ a haq fun z' r' hr' hzr' =>
    pinchTransport _ (A₂.restrict j₂) hconn₂ z r hr hzr z' r' hr' hzr'
  exact (O.chars n).false_of_test (A₂.restrict j₂) (T.orientation.restrict A₂ j₂ hOP₂)
    (sphereBasis _) (closePairBasis _) sheetsInput (A₂.restrict_faithful j₂ hfaith₂) a
    (aqc_homotopic_id _ a haq)
    fun V hV hne hinf => moveTest (T.orbitNull n) collapseInput _ a hpinch V hV hne hinf

/-- **p-adic exclusion without second countability from OpenAI's interface** (the proof of
Theorem 1.2, 06:502-516, with second countability dropped): from `OAIInterface`, `LocalInputs`
and Newman's theorem. Proposition 5.1 (`chartReductionNoSC`, from `NewmanInput`) gives a faithful
action on a connected open subset of `ℝ^n`, and `false_of_localAction` is the contradiction. -/
theorem padicExclusion_of_oaiInterface_noSC (O : OAIInterface) (T : LocalInputs O)
    (hN : NewmanInput.{u}) : HilbertSmith.Statements.PadicExclusionNoSC.{u} := by
  intro p _ n M _ _ _ _ _ _ hfaith
  obtain ⟨A₀, hconn₀, hfaith₀⟩ := chartReductionNoSC hN p n M hfaith
  exact false_of_localAction O T A₀ hconn₀ hfaith₀

/-- **p-adic exclusion from OpenAI's interface**, for second-countable manifolds (OpenAI's
Theorem 1.2 as stated): the analogue of HS_proof's `HSFormal.padicExclusion_of_inputs`. It is the
second-countable case of `padicExclusion_of_oaiInterface_noSC`. -/
theorem padicExclusion_of_oaiInterface (O : OAIInterface) (T : LocalInputs O)
    (hN : NewmanInput.{u}) : HilbertSmith.Statements.PadicExclusion.{u} :=
  fun p _ n M _ _ _ _ _ _ _ hfaith => padicExclusion_of_oaiInterface_noSC O T hN p n M hfaith

end

end HilbertSmith.Interface
