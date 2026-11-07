import HSFormal.PadicSubgroups
import HSFormal.Universe
import HilbertSmith.Statements
import HilbertSmith.Topology.InvariantOpens
import HSGeneral.Interior

/-!
# p-adic exclusion without second countability

HS_proof proves that no continuous action of `ℤ_[p]` on a connected, Hausdorff, second-countable
topological manifold is faithful (`HSFormal.Universe.padicExclusion_univ`). This file removes the
second countability, following the HS paper (HSproof.tex 757-768): a faithful action on any
connected manifold restricts to a faithful action on a connected, second-countable invariant open
subset.

## Main results

* `HSGeneral.padicExclusionNoSC_of_SC`: p-adic exclusion for second-countable manifolds implies it
  for all manifolds, in each universe.
* `HSGeneral.padicExclusionNoSC`: p-adic exclusion without second countability.
* `HSGeneral.padicExclusionWithBoundary_noSC`: the same for manifolds with boundary.

## Proof

Since `ℤ_[p]` acts faithfully, for each `j` some point `x j` is moved by `p ^ j`. As `ℤ_[p]` is
compact, `HilbertSmith.exists_vadd_invariant_opens_secondCountable` gives a connected,
second-countable invariant open set `U` containing every `x j`. The kernel of the action on `U` is
a closed subgroup of `ℤ_[p]`; if it were nontrivial it would be `p ^ m ℤ_[p]` for some `m`
(`HSFormal.padicActionKernel_eq_power`), but `p ^ m` moves `x m`. So the action on `U` is faithful,
contradicting the second-countable case.

## Declarations used from HS_proof

* `HSFormal.Universe.padicExclusion_univ`, HS_proof's headline p-adic exclusion theorem (in
  universe `u`), and the definition `HSFormal.Universe.PadicExclusionIn`, which
  `HilbertSmith.Statements.PadicExclusion` matches by definition;
* the internal lemmas `HSFormal.padicActionKernel`, `HSFormal.mem_padicActionKernel` and
  `HSFormal.padicActionKernel_eq_power` (closed subgroups of `ℤ_[p]`);
* through `HSGeneral.of_faithfulVAdd_topInterior`, HS_proof's topological interior of a manifold
  with boundary (see `HSGeneral/Interior.lean`).
-/

open Set TopologicalSpace

universe u

namespace HSGeneral

section Kernel

variable {p : ℕ} [Fact p.Prime]

/-- Under a faithful action of `ℤ_[p]`, every power of `p` moves some point. -/
theorem exists_pow_vadd_ne {X : Type*} [AddAction ℤ_[p] X] [FaithfulVAdd ℤ_[p] X] (j : ℕ) :
    ∃ x : X, (p : ℤ_[p]) ^ j +ᵥ x ≠ x := by
  by_contra! h
  exact pow_ne_zero j PadicInt.prime_p.ne_zero
    (eq_of_vadd_eq_vadd fun x => (h x).trans (zero_vadd ℤ_[p] x).symm)

/-- A continuous action of `ℤ_[p]` on a Hausdorff space is faithful as soon as every power of `p`
moves some point. -/
theorem faithfulVAdd_of_forall_exists_pow_vadd_ne {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    [AddAction ℤ_[p] Y] [ContinuousVAdd ℤ_[p] Y] (h : ∀ j : ℕ, ∃ y : Y, (p : ℤ_[p]) ^ j +ᵥ y ≠ y) :
    FaithfulVAdd ℤ_[p] Y := by
  have hker : HSFormal.padicActionKernel (p := p) (X := Y) = ⊥ := by
    by_contra hne
    obtain ⟨m, hm⟩ := HSFormal.padicActionKernel_eq_power hne
    obtain ⟨y, hy⟩ := h m
    have hpm : (p : ℤ_[p]) ^ m ∈ HSFormal.padicActionKernel (p := p) (X := Y) :=
      hm ▸ Ideal.mem_span_singleton_self _
    exact hy ((HSFormal.mem_padicActionKernel _).1 hpm y)
  refine ⟨fun {g₁ g₂} hg => ?_⟩
  have hsub : g₁ - g₂ ∈ HSFormal.padicActionKernel (p := p) (X := Y) := by
    refine (HSFormal.mem_padicActionKernel _).2 fun y => ?_
    rw [sub_eq_add_neg, add_vadd, hg, ← add_vadd, add_neg_cancel, zero_vadd]
  rwa [hker, AddSubgroup.mem_bot, sub_eq_zero] at hsub

end Kernel

/-- **p-adic exclusion without second countability, from the second-countable case.** If no
continuous action of `ℤ_[p]` on a connected, Hausdorff, second-countable manifold in `Type u` is
faithful, then the same holds without second countability. -/
theorem padicExclusionNoSC_of_SC (h : HilbertSmith.Statements.PadicExclusion.{u}) :
    HilbertSmith.Statements.PadicExclusionNoSC.{u} := by
  intro p _ n X _ _ _ _ _ _ hF
  choose x hx using exists_pow_vadd_ne (p := p) (X := X)
  obtain ⟨U, hUc, hUsc, hxU, hUinv⟩ :=
    HilbertSmith.exists_vadd_invariant_opens_secondCountable (H := EuclideanSpace ℝ (Fin n))
      (fun _ => (univ : Set ℤ_[p])) (fun _ => isCompact_univ) monotone_const
      (fun j => {x j}) (fun _ => isCompact_singleton)
  have hinv : ∀ g : ℤ_[p], ∀ y ∈ U, g +ᵥ y ∈ U := fun g => hUinv g (mem_iUnion.2 ⟨0, mem_univ g⟩)
  let := HilbertSmith.invariantAddAction U hinv
  have := HilbertSmith.continuousVAdd_invariantAddAction U hinv
  have : ConnectedSpace U := isConnected_iff_connectedSpace.mp hUc
  exact h p n U <| faithfulVAdd_of_forall_exists_pow_vadd_ne fun j =>
    ⟨⟨x j, hxU j (mem_singleton _)⟩, fun hj => hx j (congrArg Subtype.val hj)⟩

/-- **p-adic exclusion without second countability**: for every prime `p`, no continuous action
of `ℤ_[p]` on a connected, Hausdorff topological manifold without boundary is faithful. -/
theorem padicExclusionNoSC : HilbertSmith.Statements.PadicExclusionNoSC.{u} :=
  padicExclusionNoSC_of_SC HSFormal.Universe.padicExclusion_univ

/-- **p-adic exclusion for manifolds with boundary, without second countability**: for every
prime `p`, no continuous action of `ℤ_[p]` on a connected, Hausdorff topological manifold with
boundary of dimension `n + 1` is faithful. A faithful action would restrict to the interior
(`HSGeneral.of_faithfulVAdd_topInterior`), contradicting `HSGeneral.padicExclusionNoSC`. -/
theorem padicExclusionWithBoundary_noSC {X : Type*} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] {n : ℕ} [ChartedSpace (EuclideanHalfSpace (n + 1)) X]
    (p : ℕ) [Fact p.Prime] [AddAction ℤ_[p] X] [ContinuousVAdd ℤ_[p] X] :
    ¬ FaithfulVAdd ℤ_[p] X := fun _ =>
  of_faithfulVAdd_topInterior (n := n) (X := X) (G := ℤ_[p]) fun Y _ _ _ _ _ _ hY =>
    padicExclusionNoSC p (n + 1) Y hY

end HSGeneral
