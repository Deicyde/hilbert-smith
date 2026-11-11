import Mathlib
import HilbertSmithPaper.LocalData.Control.ControlMetric
import HilbertSmithPaper.LocalData.Control.OrbitSupMetricProperties
import HilbertSmithPaper.LocalData.Subgroups.PadicSubgroupsBasis
import HilbertSmithPaper.LocalData.Control.ControlQuotientMap
import HilbertSmithPaper.LocalData.Control.ControlTopology

/-!
# The orbit metric metrizes the control space

`d_T` is a metric on `T` (`d_T s s = 0`, symmetry, the triangle inequality, `d_T s t = 0 → s = t`)
whose open sets are exactly the open sets of the quotient topology: `U` is open iff every `s ∈ U`
has some `ε > 0` with `{t | d_T s t < ε} ⊆ U`.

Symmetry and the triangle inequality follow from those of `d₁` and its invariance (reindexing over
`H₁`). If `d_T (π z) (π w) = 0`, the infimum over the compact `H₁` of the continuous
`b ↦ d₁ z (b +ᵥ w)` is attained, so `z = b +ᵥ w` and `π z = π w`. For the topology: `U` is open in
the quotient iff `π⁻¹ U` is open in `Z⁺`, which `d₁` metrizes; `d_T (π z) (π w) ≤ d₁ z w` gives one
direction, and `d_T (π z) (π w) < ε` gives some `b ∈ H₁` with `d₁ z (b +ᵥ w) < ε`, the other.
-/

namespace HSP

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- `d_T` is a metric on the control space inducing its quotient topology. -/
theorem LocalDatum.dT_metric (A : LocalDatum p n D ρplus) :
    (∀ s, A.dT s s = 0) ∧ (∀ s t, A.dT s t = A.dT t s) ∧
      (∀ s t u, A.dT s u ≤ A.dT s t + A.dT t u) ∧ (∀ s t, A.dT s t = 0 → s = t) ∧
      ∀ U : Set A.T, IsOpen U ↔ ∀ s ∈ U, ∃ ε > 0, ∀ t, A.dT s t < ε → t ∈ U := by
  obtain ⟨d0, dsymm, dtri, deq, dtop⟩ := A.d₁_metric
  have dnn : ∀ z w, 0 ≤ A.d₁ z w := fun z w => by
    have := dtri z w z
    rw [d0, dsymm w z] at this
    linarith
  have bdd : ∀ z w, BddBelow (Set.range fun b : padicSubgroup p 1 =>
      A.d₁ z ((b : ℤ_[p]) +ᵥ w)) :=
    fun z w => ⟨0, by rintro _ ⟨b, rfl⟩; exact dnn _ _⟩
  have hval : ∀ z w, A.dT (A.π z) (A.π w) =
      ⨅ b : padicSubgroup p 1, A.d₁ z ((b : ℤ_[p]) +ᵥ w) := fun _ _ => rfl
  have hle : ∀ z w, A.dT (A.π z) (A.π w) ≤ A.d₁ z w := fun z w => by
    rw [hval]
    have h := ciInf_le (bdd z w) 0
    simp only [ZeroMemClass.coe_zero, zero_vadd] at h
    exact h
  have hball : ∀ z (ε : ℝ), IsOpen {w | A.d₁ z w < ε} := fun z ε =>
    (dtop _).2 fun x hx => ⟨ε - A.d₁ z x, sub_pos.2 hx, fun y hy => by
      have := dtri z x y
      change A.d₁ z x < ε at hx
      change A.d₁ z y < ε
      linarith⟩
  have hcont : ∀ z, Continuous (A.d₁ z) := fun z => by
    rw [Metric.continuous_iff']
    intro w ε hε
    filter_upwards [(hball w ε).mem_nhds (by simp [d0, hε])] with w' (hw' : A.d₁ w w' < ε)
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [dtri z w w', dtri z w' w, dsymm w w']
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro s
    induction s using Quotient.inductionOn' with
    | h z =>
      refine le_antisymm ?_ ?_
      · exact (hle z z).trans (d0 z).le
      · exact le_ciInf fun b => dnn _ _
  · intro s t
    induction s using Quotient.inductionOn' with
    | h z =>
    induction t using Quotient.inductionOn' with
    | h w =>
    change ⨅ b : padicSubgroup p 1, A.d₁ z ((b : ℤ_[p]) +ᵥ w) =
      ⨅ b : padicSubgroup p 1, A.d₁ w ((b : ℤ_[p]) +ᵥ z)
    have key : ∀ b : padicSubgroup p 1, A.d₁ z ((b : ℤ_[p]) +ᵥ w) =
        A.d₁ w (((-b : padicSubgroup p 1) : ℤ_[p]) +ᵥ z) := fun b => by
      rw [dsymm, ← A.d₁_vadd (-(b : ℤ_[p])), vadd_vadd, neg_add_cancel, zero_vadd]
      rfl
    exact (iInf_congr key).trans ((Equiv.neg _).iInf_comp
      (g := fun b : padicSubgroup p 1 => A.d₁ w ((b : ℤ_[p]) +ᵥ z)))
  · intro s t u
    induction s using Quotient.inductionOn' with
    | h z =>
    induction t using Quotient.inductionOn' with
    | h w =>
    induction u using Quotient.inductionOn' with
    | h u =>
    change ⨅ b : padicSubgroup p 1, A.d₁ z ((b : ℤ_[p]) +ᵥ u) ≤
      (⨅ b : padicSubgroup p 1, A.d₁ z ((b : ℤ_[p]) +ᵥ w)) +
        ⨅ b : padicSubgroup p 1, A.d₁ w ((b : ℤ_[p]) +ᵥ u)
    have key : ∀ b b' : padicSubgroup p 1,
        (⨅ c : padicSubgroup p 1, A.d₁ z ((c : ℤ_[p]) +ᵥ u)) ≤
          A.d₁ z ((b : ℤ_[p]) +ᵥ w) + A.d₁ w ((b' : ℤ_[p]) +ᵥ u) := fun b b' => by
      refine (ciInf_le (bdd z u) (b + b')).trans ?_
      have h1 := dtri z ((b : ℤ_[p]) +ᵥ w) (((b + b' : padicSubgroup p 1) : ℤ_[p]) +ᵥ u)
      have h2 : A.d₁ ((b : ℤ_[p]) +ᵥ w) (((b + b' : padicSubgroup p 1) : ℤ_[p]) +ᵥ u) =
          A.d₁ w ((b' : ℤ_[p]) +ᵥ u) := by
        rw [AddSubgroup.coe_add, ← vadd_vadd, A.d₁_vadd]
      linarith
    have k2 : ∀ b : padicSubgroup p 1,
        (⨅ c : padicSubgroup p 1, A.d₁ z ((c : ℤ_[p]) +ᵥ u)) - A.d₁ z ((b : ℤ_[p]) +ᵥ w) ≤
          ⨅ b' : padicSubgroup p 1, A.d₁ w ((b' : ℤ_[p]) +ᵥ u) :=
      fun b => le_ciInf fun b' => by linarith [key b b']
    have k3 : (⨅ c : padicSubgroup p 1, A.d₁ z ((c : ℤ_[p]) +ᵥ u)) -
        (⨅ b' : padicSubgroup p 1, A.d₁ w ((b' : ℤ_[p]) +ᵥ u)) ≤
          ⨅ b : padicSubgroup p 1, A.d₁ z ((b : ℤ_[p]) +ᵥ w) :=
      le_ciInf fun b => by linarith [k2 b]
    linarith
  · intro s t h
    induction s using Quotient.inductionOn' with
    | h z =>
    induction t using Quotient.inductionOn' with
    | h w =>
    change ⨅ b : padicSubgroup p 1, A.d₁ z ((b : ℤ_[p]) +ᵥ w) = 0 at h
    have : CompactSpace (padicSubgroup p 1) :=
      isCompact_iff_compactSpace.1 ((padicSubgroup_basis p).1 1).2
    have hc : Continuous fun b : padicSubgroup p 1 => A.d₁ z ((b : ℤ_[p]) +ᵥ w) :=
      (hcont z).comp (continuous_induced_rng.2 (continuous_subtype_val.vadd continuous_const))
    obtain ⟨b₀, -, hb₀⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hc.continuousOn
    have hmin : A.d₁ z ((b₀ : ℤ_[p]) +ᵥ w) = 0 :=
      le_antisymm (h ▸ le_ciInf fun b => hb₀ (Set.mem_univ b)) (dnn _ _)
    exact Quotient.sound ⟨b₀, (deq _ _ hmin).symm⟩
  · intro U
    constructor
    · intro hU s hs
      induction s using Quotient.inductionOn' with
      | h z =>
      have hpre : IsOpen (A.π ⁻¹' U) := hU
      obtain ⟨ε, hε, hεU⟩ := (dtop _).1 hpre z hs
      refine ⟨ε, hε, fun t ht => ?_⟩
      induction t using Quotient.inductionOn' with
      | h w =>
      change ⨅ b : padicSubgroup p 1, A.d₁ z ((b : ℤ_[p]) +ᵥ w) < ε at ht
      obtain ⟨b, hb⟩ := exists_lt_of_ciInf_lt ht
      have hmem := hεU _ hb
      have e : A.π ((b : ℤ_[p]) +ᵥ w) = A.π w := Quotient.sound ⟨b, rfl⟩
      change A.π w ∈ U
      rw [← e]
      exact hmem
    · intro hU
      change IsOpen (A.π ⁻¹' U)
      refine (dtop _).2 fun z hz => ?_
      obtain ⟨ε, hε, hεU⟩ := hU (A.π z) hz
      exact ⟨ε, hε, fun w hw => hεU (A.π w) ((hle z w).trans_lt hw)⟩

end HSP
