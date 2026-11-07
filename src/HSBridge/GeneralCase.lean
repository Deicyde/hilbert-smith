import HSBridge.SideBySide

/-!
# p-adic exclusion without second countability, two ways

Two unconditional proofs of `HilbertSmith.Statements.PadicExclusionNoSC`: no continuous action of
`ℤ_[p]` on a connected Hausdorff topological manifold, second countable or not, is faithful.
Neither HS_proof nor OpenAI's preprint states this. Both proofs reduce it to HS_proof's
second-countable theorem (`HSFormal.Universe.padicExclusion_univ`, restated as
`HSBridge.hs_route_univ`), in different ways:

* `HSBridge.generalCase_hs`, the HS paper's way (HSproof.tex 757-768), is Track A's
  `HSGeneral.padicExclusionNoSC`;
* `HSBridge.generalCase_oai`, OpenAI's way, goes through Proposition 5.1 as formalized in
  `HilbertSmith.Interface.chartReductionNoSC`.

Formal Conjectures' `Hilbert5.hilbert_smith_padic_formulation` is the same statement with its
binders in another order; both proofs give it (the two `example`s below).

## The HS paper's reduction: a global point-set exhaustion

`HSGeneral.padicExclusionNoSC_of_SC` keeps the whole group and shrinks the space. For each `j`, a
faithful action moves some point `x j` by `p ^ j`. Track A's
`HilbertSmith.exists_vadd_invariant_opens_secondCountable` then builds, from the whole manifold,
one connected open set `U` that contains every `x j` and is invariant under all of `ℤ_[p]`: an
increasing union of connected open sets `V j` with compact closures, where `V (j + 1)` contains
the orbit of `closure (V j)` under the compact group and the point `x (j + 1)`. The union is
σ-compact, hence second countable, and it may spread over the whole manifold: no chart is singled
out. Newman's theorem is not used. Faithfulness on `U` comes from the classification of closed
subgroups: the kernel on `U` would be `p ^ m ℤ_[p]` (HS_proof's
`HSFormal.padicActionKernel_eq_power`), but `p ^ m` moves `x m`.

## OpenAI's reduction: never leaving one chart

`HSBridge.padicExclusionNoSC_of_chartReduction` keeps one chart and shrinks the group. Proposition
5.1 (05:23-66, without the orientation step at 05:68-72) uses Newman's theorem on the saturations
`H_j B` to find a point near which no open subgroup acts trivially, and then a small connected open
set `O = H B` inside one chart, invariant under an open subgroup `H ≅ ℤ_[p]` that acts on it
faithfully. That is `ChartReductionNoSC`: a faithful action of `ℤ_[p]` on a connected open subset
of an `n`-dimensional real normed space. Such a set is second countable because the space is, and
it is an `n`-manifold through one chart; nothing else about `M` is used. The orientation step is not
needed here. The price is Newman's theorem, discharged by `HSBridge.newmanInput`.

## What each proof uses of HS_proof

Both reach HS_proof's second-countable theorem, with its L-theory. The reductions differ, as the
guarded audit at the end of the file shows:
* OpenAI's reduction, `HSBridge.padicExclusionNoSC_of_chartReduction`, uses no constant of HS_proof,
  and with `ChartReductionNoSC` discharged (`HSBridge.oai_reduction`) it uses HS_proof only through
  `HSBridge.newmanInput`, which avoids the L-theory;
* the HS paper's reduction, `HSGeneral.padicExclusionNoSC_of_SC`, uses HS_proof's classification of
  closed subgroups of `ℤ_[p]` (module `HSFormal.PadicSubgroups`), and no Newman theorem.

HS_proof's second-countable theorem itself goes through its Newman theorem, so the discharge adds no
HS_proof module to OpenAI's way: at the pin of this build, both proofs reach the same HS_proof
modules (the unguarded `#route_modules` lists).

The second-countable theorem is used in universe `0` by OpenAI's way, since the chart image lives in
a real normed space in `Type`, and in the manifold's universe by the HS paper's way.
-/

open HilbertSmith.Interface

universe u

namespace HSBridge

/-- **OpenAI's reduction of the general case** (PLAN §3.5): what §6 uses of Proposition 5.1,
without second countability, reduces p-adic exclusion in any universe to the second-countable case
in universe `0`. A faithful action on `M` gives a faithful action on a connected open subset `W` of
an `n`-dimensional real normed space `E`; `W` is Hausdorff and second countable as a subspace of
`E`, and a manifold modelled on `ℝⁿ` with the single chart `W ↪ E ≃ ℝⁿ`. -/
theorem padicExclusionNoSC_of_chartReduction (hC : ChartReductionNoSC.{u})
    (h : HilbertSmith.Statements.PadicExclusion.{0}) :
    HilbertSmith.Statements.PadicExclusionNoSC.{u} := by
  intro p _ n M _ _ _ _ _ _ hF
  obtain ⟨A, hconn, hfaith⟩ := hC p n M hF
  have : ConnectedSpace A.W := isConnected_iff_connectedSpace.1 hconn
  let e : A.E ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    ContinuousLinearEquiv.ofFinrankEq (by rw [A.finrank_eq, finrank_euclideanSpace_fin])
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin n)) A.W :=
    (e.toHomeomorph.isOpenEmbedding.comp A.isOpen.isOpenEmbedding_subtypeVal).singletonChartedSpace
  exact h p n A.W hfaith

/-- OpenAI's reduction with Proposition 5.1 proved (`chartReductionNoSC`) and Newman's theorem
discharged from HS_proof (`HSBridge.newmanInput`). It plays the part that
`HSGeneral.padicExclusionNoSC_of_SC` plays in the HS paper's way. -/
theorem oai_reduction (h : HilbertSmith.Statements.PadicExclusion.{0}) :
    HilbertSmith.Statements.PadicExclusionNoSC.{u} :=
  padicExclusionNoSC_of_chartReduction (chartReductionNoSC newmanInput) h

/-- **p-adic exclusion without second countability, the HS paper's way**: an invariant
second-countable open set built by exhaustion, then HS_proof's second-countable theorem
(Track A's `HSGeneral.padicExclusionNoSC`). -/
theorem generalCase_hs : HilbertSmith.Statements.PadicExclusionNoSC.{u} :=
  HSGeneral.padicExclusionNoSC

/-- **p-adic exclusion without second countability, OpenAI's way**: Proposition 5.1 inside one
chart (`HSBridge.oai_reduction`), then HS_proof's second-countable theorem in universe `0`
(`HSBridge.hs_route_univ`). -/
theorem generalCase_oai : HilbertSmith.Statements.PadicExclusionNoSC.{u} :=
  oai_reduction hs_route_univ.{0}

-- Formal Conjectures' statement, binders in its order, from each proof.
example {n : ℕ} {X : Type u} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] (p : ℕ) [Fact p.Prime] [AddAction ℤ_[p] X]
    [ContinuousVAdd ℤ_[p] X] : ¬ FaithfulVAdd ℤ_[p] X :=
  generalCase_hs p n X

example {n : ℕ} {X : Type u} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] (p : ℕ) [Fact p.Prime] [AddAction ℤ_[p] X]
    [ContinuousVAdd ℤ_[p] X] : ¬ FaithfulVAdd ℤ_[p] X :=
  generalCase_oai p n X

/-! ### The audit of the two reductions

The guarded checks are the stable facts; the `#route_report` lists depend on the HS_proof pin. -/

/--
info: route audit: 'HSBridge.padicExclusionNoSC_of_chartReduction' depends on no constant from
  HS_proof
-/
#guard_msgs (whitespace := lax) in
#assert_route_pure padicExclusionNoSC_of_chartReduction

/--
info: route audit: 'HSBridge.oai_reduction' depends on no constant from HS_proof except through:
  HSBridge.newmanInput
-/
#guard_msgs (whitespace := lax) in
#assert_route_pure oai_reduction allowing HSBridge.newmanInput

/--
info: route audit: 'HSGeneral.padicExclusionNoSC_of_SC' depends on constants from modules under
  'HSFormal.PadicSubgroups'
-/
#guard_msgs (whitespace := lax) in
#assert_route_reaches HSGeneral.padicExclusionNoSC_of_SC HSFormal.PadicSubgroups

/--
info: route audit: 'HSGeneral.padicExclusionNoSC_of_SC' avoids modules under HSFormal.Newman,
  HSFormal.LTheory and the constants HSFormal.Universe.padicExclusion_univ
-/
#guard_msgs (whitespace := lax) in
#assert_route_avoids HSGeneral.padicExclusionNoSC_of_SC modules [HSFormal.Newman, HSFormal.LTheory]
  constants [HSFormal.Universe.padicExclusion_univ]

#route_report padicExclusionNoSC_of_chartReduction

#route_report oai_reduction

#route_report HSGeneral.padicExclusionNoSC_of_SC

/-! ### The audit of the two proofs

Both reach HS_proof's L-theory, through its second-countable theorem. -/

/--
info: route audit: the value of 'HSBridge.generalCase_hs' depends on constants from modules under
  'HSFormal.LTheory'
-/
#guard_msgs (whitespace := lax) in
#assert_route_reaches_by_value generalCase_hs HSFormal.LTheory

/--
info: route audit: the value of 'HSBridge.generalCase_oai' depends on constants from modules under
  'HSFormal.LTheory'
-/
#guard_msgs (whitespace := lax) in
#assert_route_reaches_by_value generalCase_oai HSFormal.LTheory

#route_report generalCase_hs

#route_report generalCase_oai

#route_modules generalCase_hs front HSFormal.WeakInputs HSFormal.Reduction HSFormal.MontgomeryPrime
  HSFormal.PadicSubgroups HSFormal.PadicStabilizers HSFormal.FreePoint HSFormal.FixedData
  HSFormal.Newman.Newman HSFormal.Newman.Degree HSFormal.Inputs.GY.NSSIsLie HSFormal.Inputs.Lemma7

#route_modules generalCase_oai front HSFormal.WeakInputs HSFormal.Reduction HSFormal.MontgomeryPrime
  HSFormal.PadicSubgroups HSFormal.PadicStabilizers HSFormal.FreePoint HSFormal.FixedData
  HSFormal.Newman.Newman HSFormal.Newman.Degree HSFormal.Inputs.GY.NSSIsLie HSFormal.Inputs.Lemma7

end HSBridge
