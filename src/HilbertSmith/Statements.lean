import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Topology.Algebra.MulAction

/-!
# The statements this repository compares

This file imports Mathlib only. It states the theorems that the two routes to the Hilbert–Smith
conjecture prove, in the form both routes are compared against:

* `PadicExclusion`: no continuous action of the `p`-adic integers on a connected, Hausdorff,
  second-countable topological manifold is faithful (OpenAI's Theorem 1.2);
* `PadicExclusionNoSC`: the same without second countability (the body of Formal Conjectures'
  `hilbert_smith_padic_formulation`);
* `HilbertSmith`: a locally compact, Hausdorff, second-countable group acting continuously and
  faithfully on a connected, Hausdorff, second-countable manifold is a Lie group (OpenAI's
  Theorem 1.1);
* `HilbertSmithNoSC`: the same with no countability or separation assumption on the group and no
  second countability of the manifold.

A topological manifold of dimension `n` without boundary is a `ChartedSpace` modelled on
`EuclideanSpace ℝ (Fin n)` over its given topology; no smoothness is assumed. A group is a Lie
group if its given topology carries an atlas modelled on some `ℝ^d` that makes it a `C^∞` Lie
group, so the Lie structure induces the original topology.
-/

open scoped Manifold ContDiff

namespace HilbertSmith.Statements

universe u v

/-- `G` is a Lie group in its given topology: for some `d`, the topology of `G` carries a charted
space structure modelled on `ℝ^d` that makes `G` a `C^∞` Lie group. -/
def IsLieGroup (G : Type v) [Group G] [TopologicalSpace G] : Prop :=
  ∃ (d : ℕ) (_ : ChartedSpace (EuclideanSpace ℝ (Fin d)) G),
    LieGroup 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ G

/-- **p-adic exclusion** for second-countable manifolds: for every prime `p`, no jointly continuous
action of `ℤ_[p]` on a connected, Hausdorff, second-countable topological manifold without boundary
is faithful. -/
def PadicExclusion : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (M : Type u) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [ConnectedSpace M]
    [AddAction ℤ_[p] M] [ContinuousVAdd ℤ_[p] M], ¬ FaithfulVAdd ℤ_[p] M

/-- **p-adic exclusion** without second countability: for every prime `p`, no jointly continuous
action of `ℤ_[p]` on a connected, Hausdorff topological manifold without boundary is faithful. -/
def PadicExclusionNoSC : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [ConnectedSpace M]
    [AddAction ℤ_[p] M] [ContinuousVAdd ℤ_[p] M], ¬ FaithfulVAdd ℤ_[p] M

/-- **The Hilbert–Smith conjecture** for second-countable groups and manifolds: a locally compact,
Hausdorff, second-countable group acting continuously and faithfully on a connected, Hausdorff,
second-countable topological manifold without boundary is a Lie group. -/
def HilbertSmith : Prop :=
  ∀ (n : ℕ) (M : Type u) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [ConnectedSpace M]
    (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [T2Space G] [SecondCountableTopology G] [MulAction G M] [ContinuousSMul G M]
    [FaithfulSMul G M], IsLieGroup G

/-- **The Hilbert–Smith conjecture** without countability: a locally compact group acting
continuously and faithfully on a connected, Hausdorff topological manifold without boundary is a
Lie group. -/
def HilbertSmithNoSC : Prop :=
  ∀ (n : ℕ) (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [ConnectedSpace M]
    (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [MulAction G M] [ContinuousSMul G M] [FaithfulSMul G M], IsLieGroup G

end HilbertSmith.Statements
