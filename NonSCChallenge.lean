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
-- Modified for Deicyde/hilbert-smith: attributes omitted.
import Mathlib

/-!
# Challenge: the Hilbert–Smith conjecture without second countability

Two statements, each with proof `sorry`. This file imports only Mathlib and has no auxiliary
definitions. `NonSCSolution.lean` proves both.

* `Hilbert5.hilbert_smith_padic_formulation` is the theorem of that name in
  `FormalConjectures/HilbertProblems/5.lean` of
  [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
  (Apache-2.0, header above). Its text, including the `namespace`, `open` and `variable` lines, is
  the text there; only the `@[category …, AMS …]` attribute, which Formal Conjectures defines, is
  omitted. No second countability is assumed, and `X` lies in any universe.
* `hilbert_smith_noSC` is the Hilbert–Smith theorem with no countability assumption on `M` or
  `G` and no separation assumption on `G`, for `M` and `G` in `Type`. Its conclusion, a `C^∞` Lie
  group structure on `G` for its given topology, is the one of HS_proof's `Challenge.lean`.
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
    ¬ FaithfulVAdd ℤ_[p] X := by
  sorry

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
      LieGroup 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ G := by
  sorry
