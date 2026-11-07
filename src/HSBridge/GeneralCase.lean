import HSBridge.SideBySide
import HSGeneral.FormalConjectures

/-!
# p-adic exclusion without second countability, two ways

Two unconditional proofs of `HilbertSmith.Statements.PadicExclusionNoSC`: no continuous action of
`ℤ_[p]` on a connected Hausdorff topological manifold without boundary, second countable or not, is
faithful. HS_proof's Lean library and OpenAI's preprint state it only for second-countable
manifolds (`HSFormal.Universe.padicExclusion_univ`; 01-introduction.tex:32, 05-local-tests.tex:5).
The HS paper's main theorem (HSproof.tex 85-96) states it without second countability, and with
boundary, and reduces to the second-countable case at 757-768. Both proofs here end in HS_proof's
second-countable theorem for manifolds in `Type`, `HSFormal.padicExclusion` (restated as
`HSBridge.hs_route`), and reach it in different ways:

* `HSBridge.generalCase_hs`, the HS paper's reduction, is Track A's `HSGeneral.padicExclusionNoSC`;
* `HSBridge.generalCase_oai`, OpenAI's reduction, goes through Proposition 5.1 as formalized in
  `HilbertSmith.Interface.chartReductionNoSC`.

Only the reductions differ. Both proofs then use HS_proof's back end, its second-countable theorem
with its L-theory, and neither uses OpenAI's §6. OpenAI's own route without second countability,
`HSBridge.oai_route_noSC`, still assumes `OAIInterface` and `LocalInputs` (`Orientation`,
`AveragedTest`, `OrbitNull`).

Formal Conjectures' `Hilbert5.hilbert_smith_padic_formulation` is the same statement with its
binders in another order, and `n` and `X` implicit; both proofs give it (the two `example`s
below, stated against the pinned declaration).

## The HS paper's reduction: a global point-set exhaustion

`HSGeneral.padicExclusionNoSC_of_SC` keeps the whole group and shrinks the space. For each `j`, a
faithful action moves some point `x j` by `p ^ j`. Track A's
`HilbertSmith.exists_vadd_invariant_opens_secondCountable` then builds, from the whole manifold,
one connected open set `U` that contains every `x j` and is invariant under all of `ℤ_[p]`: an
increasing union of connected open sets `V j` with compact closures, where `V (j + 1)` contains
the orbit of `closure (V j)` under the compact group and the point `x (j + 1)`. The union is
σ-compact, hence second countable, and it may spread over the whole manifold: no chart is singled
out. Newman's theorem is not used. Faithfulness on `U` comes from the classification of closed
subgroups of `ℤ_[p]`, in HS_proof's copy: the kernel on `U` would be `p ^ m ℤ_[p]`
(`HSFormal.padicActionKernel_eq_power`), but `p ^ m` moves `x m`.

## OpenAI's reduction: never leaving one chart

`HilbertSmith.Interface.chartReductionNoSC`, used through `HSBridge.oai_reduction`, shrinks both
the space, to a set `O` inside one chart, and the group, to an open subgroup. Proposition 5.1
(05:23-66, without the orientation step at 05:68-72) uses Newman's theorem on the saturations
`H_j B` to find a point near which no open subgroup acts trivially, and then a small connected open
set `O = H B` inside one chart, invariant under an open subgroup `H ≅ ℤ_[p]`. Faithfulness of `H`
on `O` comes from the classification of closed subgroups too, in Deicyde's copy
(`HilbertSmith.closed_eq_dvd_pow`, 05:61-64). The result, `ChartReductionNoSC`, is a faithful
action of `ℤ_[p]` on a connected open subset of an `n`-dimensional real normed space.
`HSBridge.padicExclusionNoSC_of_chartReduction` then makes that set a second-countable manifold:
it is second countable because the space is, and an `n`-manifold through one chart; nothing else
about `M` is used. The orientation step is not needed here. The price is Newman's theorem,
discharged by `HSBridge.newmanInput`.

So the contrast is whose copy of the classification of closed subgroups each reduction uses, and
Newman's theorem.

## What each proof uses of HS_proof

Both reach HS_proof's second-countable theorem, with its L-theory. The reductions differ, as the
guarded audits here and in `HSBridge.SideBySide` show:
* OpenAI's reduction, `HSBridge.padicExclusionNoSC_of_chartReduction`, uses no constant of HS_proof,
  and with `ChartReductionNoSC` discharged (`HSBridge.oai_reduction`) it uses HS_proof only through
  `HSBridge.newmanInput`, which avoids the L-theory and HS_proof's closed subgroups;
* the HS paper's reduction, `HSGeneral.padicExclusionNoSC_of_SC`, uses HS_proof's classification of
  closed subgroups of `ℤ_[p]` (module `HSFormal.PadicSubgroups`), and no Newman theorem.

HS_proof's second-countable theorem itself goes through its Newman theorem (both proofs reach
`HSFormal.Newman`, guarded below), so the discharge adds no HS_proof module to OpenAI's way: at the
pin of this build, both proofs reach the same HS_proof modules (the unguarded `#route_modules`
lists).

OpenAI's way applies the second-countable theorem in universe `0`, since the chart image lives in a
real normed space in `Type`; the HS paper's way applies it in the manifold's universe, through
`HSFormal.Universe.padicExclusion_univ`. That universe-`u` theorem is itself derived from the
`Type` case (`HSFormal.Universe.padicExclusionIn_of_type`), so both proofs end in
`HSFormal.padicExclusion`.
-/

open HilbertSmith.Interface

universe u

namespace HSBridge

/-- **The last step of OpenAI's reduction of the general case** (PLAN §3.5): given what §6 uses
of Proposition 5.1 without second countability, p-adic exclusion in any universe follows from the
second-countable case in universe `0`. The proposition turns a faithful action on `M` into a
faithful action on a connected open subset `W` of an `n`-dimensional real normed space `E`; this
step makes `W` a second-countable manifold: Hausdorff and second countable as a subspace of `E`,
and modelled on `ℝⁿ` with the single chart `W ↪ E ≃ ℝⁿ`. -/
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

/-- **p-adic exclusion without second countability, the HS paper's way**: the HS paper's
reduction (an invariant second-countable open set built by exhaustion), then HS_proof's back end,
its second-countable theorem (Track A's `HSGeneral.padicExclusionNoSC`). -/
theorem generalCase_hs : HilbertSmith.Statements.PadicExclusionNoSC.{u} :=
  HSGeneral.padicExclusionNoSC

/-- **p-adic exclusion without second countability, OpenAI's way**: OpenAI's reduction
(Proposition 5.1 inside one chart, `HSBridge.oai_reduction`), then HS_proof's back end, its
second-countable theorem for manifolds in `Type` (`HSBridge.hs_route`). -/
theorem generalCase_oai : HilbertSmith.Statements.PadicExclusionNoSC.{u} :=
  oai_reduction hs_route

-- Formal Conjectures' statement, as pinned (`HSGeneral.FormalConjectures`), from each proof.
example : type_of% @Hilbert5.hilbert_smith_padic_formulation.{u} :=
  fun {n} {X} _ _ _ _ p _ _ _ => generalCase_hs p n X

example : type_of% @Hilbert5.hilbert_smith_padic_formulation.{u} :=
  fun {n} {X} _ _ _ _ p _ _ _ => generalCase_oai p n X

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

/--
info: route audit: 'HSBridge.oai_reduction' avoids modules under HSFormal.PadicSubgroups,
  HSFormal.LTheory and the constants HSFormal.padicExclusion, HSFormal.Universe.padicExclusion_univ
-/
#guard_msgs (whitespace := lax) in
#assert_route_avoids oai_reduction modules [HSFormal.PadicSubgroups, HSFormal.LTheory]
  constants [HSFormal.padicExclusion, HSFormal.Universe.padicExclusion_univ]

#route_report padicExclusionNoSC_of_chartReduction

#route_report oai_reduction

#route_report HSGeneral.padicExclusionNoSC_of_SC

/-! ### The audit of the two proofs

Both reach HS_proof's L-theory and its Newman theorem, through its second-countable theorem. -/

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

/--
info: route audit: the value of 'HSBridge.generalCase_hs' depends on constants from modules under
  'HSFormal.Newman'
-/
#guard_msgs (whitespace := lax) in
#assert_route_reaches_by_value generalCase_hs HSFormal.Newman

/--
info: route audit: the value of 'HSBridge.generalCase_oai' depends on constants from modules under
  'HSFormal.Newman'
-/
#guard_msgs (whitespace := lax) in
#assert_route_reaches_by_value generalCase_oai HSFormal.Newman

#route_report generalCase_hs

#route_report generalCase_oai

#route_modules generalCase_hs front HSFormal.WeakInputs HSFormal.Reduction HSFormal.MontgomeryPrime
  HSFormal.PadicSubgroups HSFormal.PadicStabilizers HSFormal.FreePoint HSFormal.FixedData
  HSFormal.Newman.Newman HSFormal.Newman.Degree HSFormal.Inputs.GY.NSSIsLie HSFormal.Inputs.Lemma7

#route_modules generalCase_oai front HSFormal.WeakInputs HSFormal.Reduction HSFormal.MontgomeryPrime
  HSFormal.PadicSubgroups HSFormal.PadicStabilizers HSFormal.FreePoint HSFormal.FixedData
  HSFormal.Newman.Newman HSFormal.Newman.Degree HSFormal.Inputs.GY.NSSIsLie HSFormal.Inputs.Lemma7

end HSBridge
