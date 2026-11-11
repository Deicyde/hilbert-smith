import Mathlib

/-!
# `ℤ_p` inside a compact torsion-free group

A classical input, stated over Mathlib notions with a `sorry` proof (an open statement). The
additive group `ℤ_[p]` enters as `Multiplicative ℤ_[p]`, so that a homomorphism from it to the
multiplicative group `K` is a `MonoidHom`. "No element of finite order other than `1`" is
`IsOfFinOrder g → g = 1`. The prime is existential; the instance `Fact p.Prime` that `ℤ_[p]`
needs is bound inside the existential.
-/

namespace HSP

universe v

/-- **`ℤ_p` inside a compact torsion-free group** (classical, open statement). A nontrivial compact
Hausdorff topological group with no nontrivial element of finite order receives, for some prime
`p`, a continuous injective homomorphism from the additive group `ℤ_[p]`. -/
theorem exists_padic_embedding (K : Type v) [Group K] [TopologicalSpace K]
    [IsTopologicalGroup K] [CompactSpace K] [T2Space K] [Nontrivial K]
    (htf : ∀ g : K, IsOfFinOrder g → g = 1) :
    ∃ (p : ℕ) (_ : Fact p.Prime), ∃ φ : Multiplicative ℤ_[p] →* K,
      Continuous φ ∧ Function.Injective φ := by
  sorry

end HSP
