---
article_id: af_417fd9639b40db1c1ca7302f
---

# Where second countability goes

*Does either proof need the manifold or the group to be second countable, and if not, how does it
avoid the hypothesis?*

The HS paper settles the question in one paragraph at the start of Section 8, before any geometry,
and reuses the construction in the proof of Corollary 1.2. The preprint never explains what the
hypothesis is for: both of its theorems assume second countability, and its first step moves into one chart, where the
hypothesis on the manifold holds automatically.

## HS_proof

Both of the HS paper's results are stated with no countability ([HS paper, lines 85-97](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L85-L97)).
Section 8 disposes of the issue with a point-set observation ([HS paper, lines 757-768](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L757-L768)):
when a compact group $K$ acts on a connected manifold, any $\sigma$-compact subset sits inside a
$K$-invariant, connected, second-countable open piece. Grow the piece in countably many steps
$V_0 \subset V_1 \subset \cdots$. Each step is finite work because compactness propagates: the
saturation $K\overline{V_j}$ of a compact closure is compact, as the image of $K \times \overline{V_j}$
under the action (the preprint makes the same remark, [§5, lines 112-113](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Hilbert-Smith-conjecture-in-every-finite-dimension-September-23-2026/build/sections/05-local-tests.tex#L112-L113)), and a
compact subset of a connected manifold can be fattened to a connected open set with compact closure
that finitely many charts cover, by covering it with finitely many charts and joining these by paths
([HS paper, lines 761-763](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L761-L763)). So $V_{j+1}$ is taken to be such a fattening of
$K\overline{V_j}$ together with the next compact set to be absorbed ([HS paper, lines 763-766](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L763-L766)).
The union $U = \bigcup_j V_j$ is open; it is connected as an increasing union of connected sets;
it is $K$-invariant because $KV_j \subset V_{j+1}$; and countably many charts cover it, so it is
second countable.

For $K = \mathbb{Z}_p$ acting effectively, the sets to absorb are single points: at stage $j$, add a
point that $p^j$ moves ([HS paper, line 766](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L766)).
The paper says only that the restriction stays effective. The reason is the classification it
proves a few lines later: a nonzero closed subgroup of $\mathbb{Z}_p$ is some $p^m\mathbb{Z}_p$,
because an element of least valuation $m$ has integer multiples dense in it ([HS paper, lines 774-775](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L774-L775)).
The kernel on $U$ is closed, and it cannot be $p^m\mathbb{Z}_p$, since $p^m$ moves a point of $U$.
The paper works on $U$ from then on ([HS paper, lines 767-768](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L767-L768)).
$U$ is built from the whole manifold and may spread over all of it; no chart is singled out, and
Newman's theorem is not used.

The group gets the same treatment. In the proof of Corollary 1.2 the lemma is applied to each
compact subgroup $K$ of $G$, giving invariant second-countable pieces $U \subset V$, with every
point in some such $V$ ([HS paper, lines 1369-1371](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L1369-L1371) and [line 1379](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L1379)).
The compact quotient $K/N_U$ is second countable because it embeds in the metrizable group
$\mathrm{Homeo}(U)$ ([HS paper, lines 1372-1374](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L1372-L1374)),
so the group itself never needs to be ([previous stage](groups-to-zp.md)).

## OpenAI's proof

Both theorems assume second countability: of the group and the manifold in Theorem 1.1, of the
manifold in Theorem 1.2 ([preprint, §1, lines 10-12](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Hilbert-Smith-conjecture-in-every-finite-dimension-September-23-2026/build/sections/01-introduction.tex#L10-L12) and [lines 31-33](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Hilbert-Smith-conjecture-in-every-finite-dimension-September-23-2026/build/sections/01-introduction.tex#L31-L33)).
Section 5 repeats the hypothesis when it fixes the action ([preprint, §5, lines 4-6](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Hilbert-Smith-conjecture-in-every-finite-dimension-September-23-2026/build/sections/05-local-tests.tex#L4-L6)).
Proposition 5.1 then shrinks to a neighbourhood of one point. It finds a point $x$ near which no
open subgroup acts trivially, a coordinate ball $B \ni x$ with closure inside a chart $C$, and an
open subgroup $H$ with $H\overline{B} \subset C$, and sets $O = HB$ ([preprint, §5, lines 31-60](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Hilbert-Smith-conjecture-in-every-finite-dimension-September-23-2026/build/sections/05-local-tests.tex#L31-L60)).
From then on the proof sees only $O$, an open subset of $\mathbb{R}^n$, and its stabilization
$W = O \times \mathbb{R}^{d-n}$ ([preprint, §5, lines 75-80](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Hilbert-Smith-conjecture-in-every-finite-dimension-September-23-2026/build/sections/05-local-tests.tex#L75-L80)).
The one later mention of second countability is in the proof of Lemma 5.2, which needs $W$ second
countable so that its one-point compactification is metrizable ([preprint, §5, lines 118-119](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Hilbert-Smith-conjecture-in-every-finite-dimension-September-23-2026/build/sections/05-local-tests.tex#L118-L119));
that holds because $W \subset \mathbb{R}^d$. So the argument never uses second countability of the
manifold; the preprint does not say so.

For the group, the hypothesis is handed on rather than used. The proof of Theorem 1.1 applies the
cited reduction to the given second-countable group and does not say whether the reduction needs
the hypothesis ([preprint, §6, lines 519-524](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Hilbert-Smith-conjecture-in-every-finite-dimension-September-23-2026/build/sections/06-character-classes.tex#L519-L524)).
The almost-periodic corollary checks the hypothesis, by embedding its compact group in a countable
product of copies of $M$ before applying Theorem 1.1 ([preprint, §1, lines 49-52](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Hilbert-Smith-conjecture-in-every-finite-dimension-September-23-2026/build/sections/01-introduction.tex#L49-L52)).

## Side by side

|  | HS_proof | OpenAI's proof |
| --- | --- | --- |
| Idea | Remove it: saturations of compact sets under a compact group are compact, so an increasing union of relatively compact connected open sets, each holding the saturation of the last closure, is an invariant second-countable piece; points moved by every $p^j$ keep the action effective | Keep it in the statements, never use it for the manifold: the chart step moves at once into an open subset of $\mathbb{R}^n$; for the group, hand it to the cited reduction |
| Inputs | Compactness of the group; closed subgroups of $\mathbb{Z}_p$ ([HS paper, lines 774-775](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L774-L775)); for groups, metrizability of $\mathrm{Homeo}(U)$ | Newman's theorem and closed subgroups of $\mathbb{Z}_p$ ([preprint, §5, lines 24-66](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Hilbert-Smith-conjecture-in-every-finite-dimension-September-23-2026/build/sections/05-local-tests.tex#L24-L66)) |
| Formal status | not formalized in HS_proof, whose statements assume second countability. Proved here (Track A): the manifold step as in the paper; the group step by a different argument, for groups and manifolds in `Type` | proved here from Newman's theorem (the chart step, with no second countability); the route without second countability is proved here from the interface (`δD`, `inv`, `chars`), with Lemmas 5.4 and 5.5 assumed (OrbitNull) and Newman's theorem derived here from HS_proof's proof of it for prime order (`HSBridge.newmanInput`). A reduction of the general case to the second-countable one, built here from the preprint's Proposition 5.1 (the preprint states both theorems with second countability), is proved here from Newman's theorem; the HS paper's reduction is proved here (Track A) |
| Lean | [`HilbertSmith.exists_smul_invariant_opens_secondCountable`](https://github.com/Deicyde/hilbert-smith/blob/1505120556bbe2ba3c6d4e77a0c3b0365da32abd/src/HilbertSmith/Topology/InvariantOpens.lean#L119), [`HSGeneral.padicExclusionNoSC_of_SC`](https://github.com/Deicyde/hilbert-smith/blob/1505120556bbe2ba3c6d4e77a0c3b0365da32abd/src/HSGeneral/Padic.lean#L83), [`HSGeneral.hilbertSmithNoSC`](https://github.com/Deicyde/hilbert-smith/blob/1505120556bbe2ba3c6d4e77a0c3b0365da32abd/src/HSGeneral/Group.lean#L255) | [`HilbertSmith.Interface.chartReductionNoSC`](https://github.com/Deicyde/hilbert-smith/blob/1505120556bbe2ba3c6d4e77a0c3b0365da32abd/src/HilbertSmith/Interface/ChartReduction.lean#L400), [`HSBridge.oai_route_noSC`](https://github.com/Deicyde/hilbert-smith/blob/1505120556bbe2ba3c6d4e77a0c3b0365da32abd/src/HSBridge/SideBySide.lean#L140), [`HSBridge.padicExclusionNoSC_of_chartReduction`](https://github.com/Deicyde/hilbert-smith/blob/1505120556bbe2ba3c6d4e77a0c3b0365da32abd/src/HSBridge/GeneralCase.lean#L94) |

## What is shared

- Both end on a second-countable invariant open piece on which the restricted action stays
  faithful, and both use compactness of the acting group to keep the saturation of a compact set
  under control ([HS paper, lines 763-765](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L763-L765); [preprint, §5, lines 41-43](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Hilbert-Smith-conjecture-in-every-finite-dimension-September-23-2026/build/sections/05-local-tests.tex#L41-L43) and [lines 112-113](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Hilbert-Smith-conjecture-in-every-finite-dimension-September-23-2026/build/sections/05-local-tests.tex#L112-L113)).
- Both keep faithfulness after restricting by the classification of nonzero closed subgroups of
  $\mathbb{Z}_p$ as the $p^j\mathbb{Z}_p$ ([HS paper, lines 767-775](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L767-L775); [preprint, §5, lines 61-66](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Hilbert-Smith-conjecture-in-every-finite-dimension-September-23-2026/build/sections/05-local-tests.tex#L61-L66)).

## What differs

- **Explicit or idle.** The HS paper removes the hypothesis in so many words, for the manifold
  and, through compact subgroups, for the group ([HS paper, lines 1369-1374](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L1369-L1374)).
  The preprint keeps it in its statements; for the manifold it is idle, and the text does not
  remark on it.
- **What shrinks.** The HS paper keeps all of $\mathbb{Z}_p$ and grows a piece that may spread over
  the whole manifold. The preprint shrinks both the group, to an open subgroup $H$, and the space,
  to $O = HB$ inside one chart ([preprint, §5, lines 52-60](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Hilbert-Smith-conjecture-in-every-finite-dimension-September-23-2026/build/sections/05-local-tests.tex#L52-L60)).
  The HS paper passes to a chart and a subgroup $p^j\mathbb{Z}_p$ only later, after a free point
  is found ([HS paper, lines 782-787](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L782-L787);
  [one chart](one-chart.md)).
- **Newman's theorem.** The HS exhaustion needs none; the preprint's chart step rests on it
  ([preprint, §5, lines 24-50](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Hilbert-Smith-conjecture-in-every-finite-dimension-September-23-2026/build/sections/05-local-tests.tex#L24-L50)).
- **The group.** The HS paper never needs a second-countable group; the preprint assumes one and
  passes it to a cited reduction ([preprint, §6, lines 523-524](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Hilbert-Smith-conjecture-in-every-finite-dimension-September-23-2026/build/sections/06-character-classes.tex#L523-L524)).

## Read further

- In this book: [Invariant chart subset](../local-tests/chart-reduction.md),
  [Closed subgroups of $\mathbb{Z}_p$](../background/padic-subgroups.md),
  [Newman rigidity](../background/newman-rigidity.md).
- In this chapter: [The theorems without second countability](general-case.md),
  [One chart and a small subgroup](one-chart.md),
  [From locally compact groups to $\mathbb{Z}_p$](groups-to-zp.md).
- In HSWiki: [Main theorems](https://deicyde.github.io/hs-proof-wiki/roadmap/main-theorems/index.html),
  which assumes second countability throughout; its [coverage contract](https://deicyde.github.io/hs-proof-wiki/coverage/index.html)
  marks both of the paper's countability reductions as not used.

## Sources

- [HS paper, lines 757-768: the invariant second-countable submanifold](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L757-L768)
- [HS paper, lines 770-780: closed subgroups of $\mathbb{Z}_p$, in the free-point lemma](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L770-L780)
- [HS paper, lines 1367-1381: compact subgroups in the proof of Corollary 1.2](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L1367-L1381)
- [Preprint, §1, lines 9-55: the hypotheses, and the almost-periodic corollary](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Hilbert-Smith-conjecture-in-every-finite-dimension-September-23-2026/build/sections/01-introduction.tex#L9-L55)
- [Preprint, §5, lines 1-133: Proposition 5.1 and Lemma 5.2](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Hilbert-Smith-conjecture-in-every-finite-dimension-September-23-2026/build/sections/05-local-tests.tex#L1-L133)
- [Preprint, §6, lines 518-527: proof of Theorem 1.1](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Hilbert-Smith-conjecture-in-every-finite-dimension-September-23-2026/build/sections/06-character-classes.tex#L518-L527)
