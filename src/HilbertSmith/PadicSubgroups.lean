import Mathlib

open Set Topology Filter Metric

namespace HilbertSmith

variable (p : ℕ) [Fact p.Prime]

/-- Integers are dense in `ℤ_[p]`, by reading digits off `toZModPow`. -/
theorem denseRange_intCast : DenseRange ((↑) : ℤ → ℤ_[p]) := by
  intro x
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hp1 : (1:ℝ) < p := by
    have h := (Fact.out : p.Prime).one_lt
    exact_mod_cast h
  have hp0' : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / ε) hp1
  have hpos : (0:ℝ) < (p:ℝ)^k := by
    have hp0 : (0:ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
    exact pow_pos hp0 k
  have hpk : (p:ℝ)^(-k:ℤ) < ε := by
    rw [zpow_neg, zpow_natCast, ← one_div, one_div_lt hpos hε]
    exact hk
  have _nz : NeZero (p^k) := ⟨pow_ne_zero k hp0'⟩
  set a : ZMod (p^k) := PadicInt.toZModPow k x with ha
  have hval : ((a.val : ℕ) : ZMod (p^k)) = a := by
    simp only [ZMod.natCast_val, ZMod.cast_id]
  refine ⟨(a.val : ℤ), Set.mem_range_self _, ?_⟩
  have hm : ((((a.val : ℕ)) : ℤ) : ℤ_[p]) = ((a.val : ℕ) : ℤ_[p]) := by norm_cast
  rw [dist_eq_norm, hm]
  have h0 : PadicInt.toZModPow k (x - ((a.val : ℕ) : ℤ_[p])) = 0 := by
    rw [map_sub, show PadicInt.toZModPow k x = a from rfl, map_natCast, hval, sub_self]
  have hspan : x - ((a.val : ℕ) : ℤ_[p]) ∈ Ideal.span ({(p:ℤ_[p])^k} : Set ℤ_[p]) := by
    rw [← PadicInt.ker_toZModPow k]
    exact RingHom.mem_ker.mpr h0
  by_cases hzero : x - ((a.val : ℕ) : ℤ_[p]) = 0
  · rw [hzero, norm_zero]
    exact hε
  · have hle : k ≤ (x - ((a.val : ℕ) : ℤ_[p])).valuation :=
      (PadicInt.mem_span_pow_iff_le_valuation _ hzero k).mp hspan
    have hnorm : ‖x - ((a.val : ℕ) : ℤ_[p])‖ ≤ (p:ℝ)^(-k:ℤ) :=
      (PadicInt.norm_le_pow_iff_le_valuation _ hzero k).mpr hle
    exact lt_of_le_of_lt hnorm hpk

section Submodule

variable {H : AddSubgroup ℤ_[p]}

/-- A closed subgroup is stable under `ℤ_[p]`-scaling: approximate by integers. -/
theorem closed_smul_mem (hH : IsClosed (H : Set ℤ_[p])) {x : ℤ_[p]} (hx : x ∈ H)
    (c : ℤ_[p]) : c • x ∈ H := by
  have hdense : Dense (Set.range ((↑) : ℤ → ℤ_[p])) := denseRange_intCast p
  have hclosed : closure (Set.range ((↑) : ℤ → ℤ_[p])) = univ := hdense.closure_eq
  have hcont : Continuous (fun d : ℤ_[p] => d * x) := continuous_id.mul continuous_const
  have hsub : (fun d : ℤ_[p] => d * x) '' Set.univ ⊆ (H : Set ℤ_[p]) := by
    rw [← hclosed]
    refine (image_closure_subset_closure_image hcont).trans (closure_minimal ?_ hH)
    rintro _ ⟨d, ⟨m, rfl⟩, rfl⟩
    show (((m : ℤ_[p]) * x) ∈ (H : Set ℤ_[p]))
    rw [← zsmul_eq_mul]
    exact H.zsmul_mem hx m
  have hmem : (fun d : ℤ_[p] => d * x) c ∈ (H : Set ℤ_[p]) :=
    hsub ⟨c, Set.mem_univ c, rfl⟩
  simpa [smul_eq_mul] using hmem

end Submodule

section Classification

variable {H : AddSubgroup ℤ_[p]}

/-- A nonzero closed subgroup is cut out by valuations above a minimum. -/
theorem closed_eq_dvd_pow (hHclosed : IsClosed (H : Set ℤ_[p])) (hHne : H ≠ ⊥) :
    ∃ j, ∀ x, x ∈ H ↔ (p:ℤ_[p])^j ∣ x := by
  have _c := Classical.propDecidable
  have hne : ∃ x ∈ H, x ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hHne
    ext x
    simp only [AddSubgroup.mem_bot]
    constructor
    · exact fun hx => hcon x hx
    · intro hx; rw [hx]; exact H.zero_mem
  obtain ⟨x₀, hx₀H, hx₀0⟩ := hne
  set P : ℕ → Prop := fun n => ∃ x ∈ H, x ≠ 0 ∧ x.valuation = n with hP
  have hex : ∃ n, P n := ⟨x₀.valuation, x₀, hx₀H, hx₀0, rfl⟩
  set j := Nat.find hex with hj
  obtain ⟨x, hxH, hx0, hxj⟩ := Nat.find_spec hex
  have hxeq : x = ((PadicInt.unitCoeff hx0 : ℤ_[p]ˣ) : ℤ_[p]) * (p:ℤ_[p])^j := by
    rw [hj, ← hxj]; exact PadicInt.unitCoeff_spec hx0
  obtain ⟨u, hu_eq⟩ : ∃ u : ℤ_[p]ˣ, x = (u : ℤ_[p]) * (p:ℤ_[p])^j :=
    ⟨PadicInt.unitCoeff hx0, hxeq⟩
  have hpj : (p:ℤ_[p])^j ∈ H := by
    have hcalc : (p:ℤ_[p])^j = (((u⁻¹ : ℤ_[p]ˣ)) : ℤ_[p]) * x := by
      have h1 : ((((u⁻¹ * u : ℤ_[p]ˣ))) : ℤ_[p]) * (p:ℤ_[p])^j
          = (p:ℤ_[p])^j := by
        rw [inv_mul_cancel]; simp
      have h2 : ((((u⁻¹ * u : ℤ_[p]ˣ))) : ℤ_[p]) * (p:ℤ_[p])^j
          = (((u⁻¹ : ℤ_[p]ˣ)) : ℤ_[p]) * x := by
        rw [hu_eq]; push_cast; ring
      rw [h1] at h2; exact h2
    rw [hcalc]
    have hsm := closed_smul_mem p hHclosed hxH ((((u⁻¹ : ℤ_[p]ˣ))) : ℤ_[p])
    simpa [smul_eq_mul] using hsm
  refine ⟨j, fun h => ?_⟩
  constructor
  · intro hhH
    by_cases hh0 : h = 0
    · simp [hh0]
    · have hle : j ≤ h.valuation := Nat.find_le (h := hex) ⟨h, hhH, hh0, rfl⟩
      have hpow : (p:ℤ_[p])^j ∣ (p:ℤ_[p])^(h.valuation) :=
        ⟨(p:ℤ_[p])^(h.valuation - j), by rw [← pow_add, Nat.add_sub_cancel' hle]⟩
      have hdvd : (p:ℤ_[p])^j ∣ ((PadicInt.unitCoeff hh0 : ℤ_[p]ˣ) : ℤ_[p]) * (p:ℤ_[p])^(h.valuation) := by
        obtain ⟨c, hc⟩ := hpow
        refine ⟨((PadicInt.unitCoeff hh0 : ℤ_[p]ˣ) : ℤ_[p]) * c, ?_⟩
        rw [hc]; ring
      rwa [PadicInt.unitCoeff_spec hh0]
  · rintro ⟨c, rfl⟩
    have heq : (p:ℤ_[p])^j * c = c • (p:ℤ_[p])^j := by rw [mul_comm, smul_eq_mul]
    rw [heq]
    exact closed_smul_mem p hHclosed hpj c

end Classification

section Openness

/-- The `p^j`-multiples form an open set: they are a metric ball. -/
theorem isOpen_dvd_pow (j : ℕ) :
    IsOpen ({x : ℤ_[p] | (p:ℤ_[p])^j ∣ x}) := by
  have hset : {x : ℤ_[p] | (p:ℤ_[p])^j ∣ x}
      = Metric.ball (0 : ℤ_[p]) ((p : ℝ) ^ (-(j : ℤ) + 1)) := by
    ext x
    simp only [Set.mem_ofPred_eq, Metric.mem_ball, dist_zero_right]
    rw [← Ideal.mem_span_singleton, ← PadicInt.norm_le_pow_iff_mem_span_pow,
      PadicInt.norm_le_pow_iff_norm_lt_pow_add_one]
  rw [hset]
  exact Metric.isOpen_ball

end Openness

section Quotient

/-- `toZModPow` is surjective: every residue class has an integer lift. -/
theorem toZModPow_surjective (k : ℕ) :
    Function.Surjective (PadicInt.toZModPow k : ℤ_[p] → ZMod (p^k)) :=
  ZMod.ringHom_surjective _

/-- The quotient of `ℤ_[p]` by `p^j` is `ZMod (p^j)`. -/
noncomputable def quotientSpanPowEquiv (j : ℕ) :
    (ℤ_[p] ⧸ Ideal.span {(p:ℤ_[p])^j}) ≃+* ZMod (p^j) :=
  (Ideal.quotEquivOfEq (PadicInt.ker_toZModPow j).symm).trans <|
    RingHom.quotientKerEquivOfSurjective (ZMod.ringHom_surjective _)

end Quotient

end HilbertSmith
