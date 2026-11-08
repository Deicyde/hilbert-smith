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
* `PadicExclusionNoSC`: the same without second countability (equivalent to Formal Conjectures'
  `hilbert_smith_padic_formulation`, whose binders come in another order, with `n` and `X`
  implicit);
* `HilbertSmith`: a locally compact, Hausdorff, second-countable group acting continuously and
  faithfully on a connected, Hausdorff, second-countable manifold is a Lie group (OpenAI's
  Theorem 1.1);
* `HilbertSmithNoSC`: the same with no countability or separation assumption on the group and no
  second countability of the manifold.

Here a manifold of dimension `n` is a Hausdorff space together with an atlas of charts, for its
own topology, onto open subsets of `ℝ^n` (`EuclideanSpace ℝ (Fin n)`); no differentiable
structure is assumed. A Lie group is a group whose own topology carries an atlas, modelled on a
Euclidean space, in which multiplication and inversion are smooth.

The binder lists of `PadicExclusion` and `HilbertSmith` deliberately coincide with those of
HS_proof's `HSFormal.Universe.PadicExclusionIn` and `HSFormal.Universe.HilbertSmithIn`, so the
comparisons with HS_proof close by `Iff.rfl`.
-/

open scoped Manifold ContDiff

namespace HilbertSmith.Statements

universe u v

/-- `G` is a Lie group for the topology it already has: there are a dimension `d` and an atlas of
charts from `G` to `ℝ^d`, compatible with that topology, for which the group operations are
`C^∞`. -/
def IsLieGroup (G : Type v) [Group G] [TopologicalSpace G] : Prop :=
  ∃ (d : ℕ) (_ : ChartedSpace (EuclideanSpace ℝ (Fin d)) G),
    LieGroup 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ G

/-- **p-adic exclusion** (OpenAI's Theorem 1.2). Fix a prime `p` and a topological manifold
without boundary that is connected, Hausdorff and second countable. For any jointly continuous
action of `ℤ_[p]` on it, some nonzero `p`-adic integer acts as the identity, so the action is not
faithful. (Dimension `0` is allowed: the manifold is then a point.) -/
def PadicExclusion : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (M : Type u) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [ConnectedSpace M]
    [AddAction ℤ_[p] M] [ContinuousVAdd ℤ_[p] M], ¬ FaithfulVAdd ℤ_[p] M

/-- **p-adic exclusion** without second countability: OpenAI's Theorem 1.2 with the
second-countability hypothesis on the manifold dropped. Whenever `ℤ_[p]`, for a prime `p`, acts
jointly continuously on a connected Hausdorff topological manifold without boundary, some nonzero
element acts as the identity, so the action is not faithful. -/
def PadicExclusionNoSC : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [ConnectedSpace M]
    [AddAction ℤ_[p] M] [ContinuousVAdd ℤ_[p] M], ¬ FaithfulVAdd ℤ_[p] M

/-- **The Hilbert–Smith conjecture** (OpenAI's Theorem 1.1). Suppose a topological group `G`
that is locally compact, Hausdorff and second countable acts jointly continuously on a
topological manifold `M` without boundary that is connected, Hausdorff and second countable, and
that only the identity of `G` fixes every point of `M`. Then `G` is a Lie group. (Dimension `0` is
allowed: `M` is then a point and `G` is trivial.) -/
def HilbertSmith : Prop :=
  ∀ (n : ℕ) (M : Type u) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [ConnectedSpace M]
    (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [T2Space G] [SecondCountableTopology G] [MulAction G M] [ContinuousSMul G M]
    [FaithfulSMul G M], IsLieGroup G

/-- **The Hilbert–Smith conjecture** without countability: a locally compact group acting
continuously and faithfully on a connected, Hausdorff topological manifold without boundary is a
Lie group. This repository proves it only for groups and manifolds in `Type`
(`HilbertSmithNoSC.{0, 0}`). -/
def HilbertSmithNoSC : Prop :=
  ∀ (n : ℕ) (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [ConnectedSpace M]
    (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [MulAction G M] [ContinuousSMul G M] [FaithfulSMul G M], IsLieGroup G

end HilbertSmith.Statements
