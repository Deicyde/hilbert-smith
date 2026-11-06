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
import HSGeneral.Padic

/-!
# The p-adic formulation of the Hilbert–Smith conjecture, from Formal Conjectures

This file restates `Hilbert5.hilbert_smith_padic_formulation` from Formal Conjectures
(`FormalConjectures/HilbertProblems/5.lean`, Apache-2.0, header above) and proves it. In Formal
Conjectures `n` is a section variable `{n : ℕ}`; here it is an implicit binder, which gives the same
statement. The proof is `HSGeneral.padicExclusionNoSC`.
-/

namespace Hilbert5

/-- **p-adic formulation**: the p-adic integers `ℤ_[p]` cannot act continuously and faithfully
on a connected finite-dimensional topological manifold. -/
theorem hilbert_smith_padic_formulation {n : ℕ} {X : Type*}
    [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
    (p : ℕ) [Fact p.Prime] [AddAction ℤ_[p] X] [ContinuousVAdd ℤ_[p] X] :
    ¬ FaithfulVAdd ℤ_[p] X :=
  HSGeneral.padicExclusionNoSC p n X

end Hilbert5
