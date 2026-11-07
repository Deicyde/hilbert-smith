/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
-- Modified for Deicyde/hilbert-smith: attributes omitted; proof added.
import Mathlib
import HSGeneral.Group
import HSGeneral.Padic

/-!
# Solution to `NonSCChallenge.lean`

The two statements are copied verbatim from `NonSCChallenge.lean` and proved from `HSGeneral`:

* `Hilbert5.hilbert_smith_padic_formulation` by `HSGeneral.padicExclusionNoSC`, which reduces it
  to HS_proof's `HSFormal.Universe.padicExclusion_univ` through an invariant second-countable open
  subset;
* `hilbert_smith_noSC` by `HSGeneral.hilbertSmithNoSC`, which is
  `HSGeneral.hilbertSmithNoSC_of_padicExclusion HSFormal.padicExclusion`.

This file imports `HSGeneral.Padic` and `HSGeneral.Group` rather than `HSGeneral`, because
`HSGeneral.FormalConjectures` already declares `Hilbert5.hilbert_smith_padic_formulation`.
`import Mathlib` is not needed by the proofs. It makes the imports of this file a superset of those
of `NonSCChallenge.lean`, which SafeVerify requires.
-/

namespace Hilbert5

open scoped Manifold ContDiff Bundle

variable {G : Type*} [Group G] [TopologicalSpace G] {n : ℕ}

/-- **p-adic formulation**: the p-adic integers `ℤ_[p]` cannot act continuously and faithfully
on a connected finite-dimensional topological manifold. This is equivalent to
`hilbert_smith_conjecture` by the Gleason–Yamabe theorem together with Newman's theorem on
periodic transformations of manifolds. -/
theorem hilbert_smith_padic_formulation {X : Type*}
    [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
    (p : ℕ) [Fact p.Prime] [AddAction ℤ_[p] X] [ContinuousVAdd ℤ_[p] X] :
    ¬ FaithfulVAdd ℤ_[p] X :=
  HSGeneral.padicExclusionNoSC p n X

end Hilbert5

open scoped Manifold ContDiff

/-- **The Hilbert–Smith theorem without countability.** A locally compact topological group `G`
acting continuously and faithfully on a connected, Hausdorff topological `n`-manifold `M` (without
boundary) is a Lie group: for some `d`, `G` carries a `C^∞` atlas modelled on `ℝᵈ`, whose charts
are homeomorphisms for the given topology of `G`, for which multiplication and inversion are
`C^∞`. Neither `M` nor `G` is assumed second countable, and `G` is not assumed Hausdorff. -/
theorem hilbert_smith_noSC (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [ConnectedSpace M]
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [MulAction G M] [ContinuousSMul G M] [FaithfulSMul G M] :
    ∃ (d : ℕ) (_ : ChartedSpace (EuclideanSpace ℝ (Fin d)) G),
      LieGroup 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ G :=
  HSGeneral.hilbertSmithNoSC n M G
