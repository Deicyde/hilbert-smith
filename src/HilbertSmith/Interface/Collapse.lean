import HilbertSmith.Interface.LocalInputs

/-!
# Lemma 5.2: collapse and compactification

OpenAI's Lemma 5.2 (statement 05:88-103, proof 05:105-133): the collapse `c : S^d → W⁺` is
continuous, the action extends to a jointly continuous action on `W⁺` fixing `∞`, and `W⁺` and
its orbit spaces by closed subgroups are compact metrizable.

Deicyde's `HilbertSmith/CollapseCompactification.lean` proves all of it for a multiplicative
action of a compact group: `HilbertSmith.continuous_collapse`,
`HilbertSmith.continuousSMul_onePoint` (05:112-116), `HilbertSmith.metrizableSpace_onePoint` and
`HilbertSmith.metrizableSpace_orbitQuotient` (05:118-132). This file passes to the additive action
of `ℤ_[p]` of a `LocalAction`, through `Multiplicative ℤ_[p]`, and proves the route's input
`HilbertSmith.Interface.CollapseInput`.
-/

namespace HilbertSmith.Interface

open Topology Set

namespace LocalAction

variable {p : ℕ} [Fact p.Prime] {k : ℕ} (A : LocalAction p k)

/-- The action of `ℤ_[p]` on `W`, written multiplicatively. -/
@[instance_reducible]
def mulAct : MulAction (Multiplicative ℤ_[p]) A.W where
  smul g w := g.toAdd +ᵥ w
  one_smul w := zero_vadd ℤ_[p] w
  mul_smul g h w := add_vadd g.toAdd h.toAdd w

/-- The multiplicative action is jointly continuous. -/
theorem continuousSMul_mulAct :
    letI := A.mulAct
    ContinuousSMul (Multiplicative ℤ_[p]) A.W :=
  letI := A.mulAct
  ⟨continuous_vadd.comp (continuous_toAdd.prodMap continuous_id)⟩

/-- **The extended action on `W⁺` is jointly continuous** (Lemma 5.2, 05:112-116), from Deicyde's
`HilbertSmith.continuousSMul_onePoint` for the multiplicative action. -/
theorem continuousVAdd_onePoint : ContinuousVAdd ℤ_[p] (OnePoint A.W) := by
  let _ := A.mulAct
  have := A.continuousSMul_mulAct
  have h := (HilbertSmith.continuousSMul_onePoint (G := Multiplicative ℤ_[p]) A.W).continuous_smul
  refine ⟨?_⟩
  have h' := h.comp (continuous_ofAdd.prodMap continuous_id)
  convert h' using 1
  funext ⟨g, x⟩
  induction x using OnePoint.rec with
  | infty => rfl
  | coe w => rfl

/-- The orbit relation of `ℤ_[p]` on `W⁺` is that of the whole group `Multiplicative ℤ_[p]`,
viewed as its top subgroup, for Deicyde's action on `W⁺`. -/
theorem orbitRel_eq :
    letI := A.mulAct
    MulAction.orbitRel (⊤ : Subgroup (Multiplicative ℤ_[p])) (OnePoint A.W) =
      AddAction.orbitRel ℤ_[p] (OnePoint A.W) := by
  let _ := A.mulAct
  ext x y
  rw [MulAction.orbitRel_apply, AddAction.orbitRel_apply, MulAction.mem_orbit_iff,
    AddAction.mem_orbit_iff]
  constructor
  · rintro ⟨⟨g, -⟩, rfl⟩
    refine ⟨g.toAdd, ?_⟩
    induction y using OnePoint.rec with
    | infty => rfl
    | coe w => rfl
  · rintro ⟨g, rfl⟩
    refine ⟨⟨Multiplicative.ofAdd g, Subgroup.mem_top _⟩, ?_⟩
    induction y using OnePoint.rec with
    | infty => rfl
    | coe w => rfl

/-- **The orbit space `Y = W⁺/ℤ_[p]` is metrizable** (Lemma 5.2, 05:118-132), from Deicyde's
`HilbertSmith.metrizableSpace_orbitQuotient` for the top subgroup of `Multiplicative ℤ_[p]`. -/
theorem metrizableSpace_Y : TopologicalSpace.MetrizableSpace A.Y := by
  let _ := A.mulAct
  have := A.continuousSMul_mulAct
  have h := HilbertSmith.metrizableSpace_orbitQuotient (G := Multiplicative ℤ_[p]) A.W ⊤
    A.isOpen (by simp)
  change TopologicalSpace.MetrizableSpace (Quotient (AddAction.orbitRel ℤ_[p] (OnePoint A.W)))
  rwa [← A.orbitRel_eq]

end LocalAction

/-- **Lemma 5.2** for every local action: the route's input `CollapseInput`, proved. -/
theorem collapseInput : CollapseInput :=
  fun A => ⟨A.continuousVAdd_onePoint, A.metrizableSpace_Y⟩

end HilbertSmith.Interface
