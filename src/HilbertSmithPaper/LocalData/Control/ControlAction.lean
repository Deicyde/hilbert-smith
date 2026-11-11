import Mathlib
import HilbertSmithPaper.LocalData.Control.ControlSpace

/-!
# The cyclic action on the control space

`C_p = ZMod p` acts on the control space `T = Z⁺ / H₁` by `q₁(a) +ᵥ π z = π (a +ᵥ z)`, where
`q₁ = PadicInt.toZMod : ℤ_[p] → ZMod p` is reduction modulo `p`, whose kernel is `H₁`.

## Encoding

The action of `c : ZMod p` is defined with the representative `c.val ∈ {0, …, p - 1}`:
`c +ᵥ π z = π (c.val +ᵥ z)`; this is well defined because `ℤ_[p]` is abelian, so `H₁`-orbits go to
`H₁`-orbits. The formula for an arbitrary lift, `π (a +ᵥ z) = q₁(a) +ᵥ π z`, is the companion
`HSP.LocalDatum.π_vadd`; it uses that `a - q₁(a).val ∈ H₁`, i.e. that the kernel of reduction
modulo `p` is `H₁` (Mathlib: `PadicInt.toZMod_spec`, `PadicInt.maximalIdeal_eq_span_p`).
-/

namespace HSP

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

private lemma rel_vadd (A : LocalDatum p n D ρplus) (a : ℤ_[p]) {z z' : A.Zplus}
    (h : AddAction.orbitRel (padicSubgroup p 1) A.Zplus z z') :
    AddAction.orbitRel (padicSubgroup p 1) A.Zplus (a +ᵥ z) (a +ᵥ z') := by
  obtain ⟨b, rfl⟩ := h
  refine ⟨b, ?_⟩
  change (b : ℤ_[p]) +ᵥ (a +ᵥ z') = a +ᵥ ((b : ℤ_[p]) +ᵥ z')
  rw [vadd_vadd, vadd_vadd, add_comm]

private lemma π_eq_of_sub_mem (A : LocalDatum p n D ρplus) {a a' : ℤ_[p]}
    (h : a - a' ∈ padicSubgroup p 1) (z : A.Zplus) : A.π (a +ᵥ z) = A.π (a' +ᵥ z) := by
  apply Quotient.sound
  refine ⟨⟨a - a', h⟩, ?_⟩
  change (a - a') +ᵥ (a' +ᵥ z) = a +ᵥ z
  rw [vadd_vadd, sub_add_cancel]

private lemma val_add_sub_mem (c d : ZMod p) :
    ((c + d).val : ℤ_[p]) - ((c.val : ℤ_[p]) + d.val) ∈ padicSubgroup p 1 := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rw [ZMod.val_add]
  set m := (c.val + d.val) % p
  set q := (c.val + d.val) / p
  have h := congrArg (Nat.cast : ℕ → ℤ_[p]) (Nat.mod_add_div (c.val + d.val) p)
  push_cast at h
  change (p : ℤ_[p]) ^ 1 ∣ _
  exact ⟨-(q : ℤ_[p]), by linear_combination h⟩

/-- The cyclic action of `C_p = ZMod p` on the control space: `c +ᵥ π z = π (c.val +ᵥ z)`. -/
noncomputable instance LocalDatum.instAddActionT (A : LocalDatum p n D ρplus) :
    AddAction (ZMod p) A.T where
  vadd c := Quotient.map' (fun z : A.Zplus => ((c.val : ℕ) : ℤ_[p]) +ᵥ z)
    fun _ _ h => rel_vadd A _ h
  zero_vadd t := by
    induction t using Quotient.inductionOn' with
    | h z =>
      change A.π (((0 : ZMod p).val : ℤ_[p]) +ᵥ z) = A.π z
      simp [ZMod.val_zero]
  add_vadd c d t := by
    induction t using Quotient.inductionOn' with
    | h z =>
      change A.π (((c + d).val : ℤ_[p]) +ᵥ z) = A.π ((c.val : ℤ_[p]) +ᵥ ((d.val : ℤ_[p]) +ᵥ z))
      rw [vadd_vadd]
      exact π_eq_of_sub_mem A (val_add_sub_mem c d) z

/-- The action is `q₁(a) +ᵥ π z = π (a +ᵥ z)` for every `a ∈ ℤ_[p]`. -/
theorem LocalDatum.π_vadd (A : LocalDatum p n D ρplus) (a : ℤ_[p]) (z : A.Zplus) :
    A.π (a +ᵥ z) = PadicInt.toZMod a +ᵥ A.π z := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  change A.π (a +ᵥ z) = A.π (((PadicInt.toZMod a).val : ℤ_[p]) +ᵥ z)
  apply π_eq_of_sub_mem
  have h := PadicInt.toZMod_spec a
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton, ZMod.cast_eq_val] at h
  change (p : ℤ_[p]) ^ 1 ∣ _
  rwa [pow_one]

end HSP
