import Mathlib
import HilbertSmithPaper.LocalData.Subgroups.PadicSubgroups

/-!
# Closed subgroups of `ℤ_p`

Every nonzero closed additive subgroup of `ℤ_[p]` is some `H_j`. The integers are dense, so a
closed subgroup is an ideal, and the nonzero ideals of `ℤ_[p]` are the `p^j ℤ_[p]`
(`PadicInt.ideal_eq_span_pow_p`, which packages the minimal-valuation argument).
-/

namespace HSP

/-- A nonzero closed additive subgroup of `ℤ_[p]` equals `H_j` for some `j`. -/
theorem closed_eq_padicSubgroup {p : ℕ} [Fact p.Prime] (K : AddSubgroup ℤ_[p])
    (hK : IsClosed (K : Set ℤ_[p])) (h0 : K ≠ ⊥) : ∃ j, K = padicSubgroup p j := by
  have hmul : ∀ c x : ℤ_[p], x ∈ K → c * x ∈ K := by
    intro c x hx
    have hcl : IsClosed {c : ℤ_[p] | c * x ∈ K} :=
      hK.preimage (continuous_id.mul continuous_const)
    have hint : Set.range (Int.cast : ℤ → ℤ_[p]) ⊆ {c | c * x ∈ K} := by
      rintro _ ⟨m, rfl⟩
      simpa [zsmul_eq_mul] using K.zsmul_mem hx m
    exact closure_minimal hint hcl
      (by rw [(PadicInt.denseRange_intCast (p := p)).closure_range]; trivial)
  let I : Ideal ℤ_[p] :=
    { carrier := K
      add_mem' := K.add_mem
      zero_mem' := K.zero_mem
      smul_mem' := fun c x hx => hmul c x hx }
  have hI : I ≠ ⊥ := by
    intro h
    apply h0
    ext x
    refine ⟨fun hx => ?_, fun hx => ?_⟩
    · have hxI : x ∈ I := hx
      rw [h, Ideal.mem_bot] at hxI
      simp [hxI]
    · rw [AddSubgroup.mem_bot] at hx
      subst hx
      exact K.zero_mem
  obtain ⟨j, hj⟩ := PadicInt.ideal_eq_span_pow_p hI
  refine ⟨j, ?_⟩
  ext x
  have hx : x ∈ I ↔ x ∈ Ideal.span {(p : ℤ_[p]) ^ j} := by rw [hj]
  rw [Ideal.mem_span_singleton] at hx
  exact hx

end HSP
