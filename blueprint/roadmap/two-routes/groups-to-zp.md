---
article_id: af_7790eb5a11e67f77ecfa3679
---

# From locally compact groups to $\mathbb{Z}_p$

*How does a locally compact group that acts faithfully but is not a Lie group give a faithful
action of $\mathbb{Z}_p$?*

In both papers this is the last step, taken after $p$-adic exclusion is proved: it turns the
theorem about $\mathbb{Z}_p$ into Hilbert–Smith. The HS paper writes most of it out, as the proof
of its Corollary 1.2; written out, the argument never needs the group to be second countable. The
preprint cites it in one paragraph, as the proof of its Theorem 1.1.

## HS_proof

The introduction calls this the standard reduction, built from the structure of locally compact
groups and Newman's theorem ([HS paper, lines 100-101](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L100-L101)).
The proof of Corollary 1.2 ([HS paper, lines 1367-1391](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L1367-L1391)) runs in three moves once the
point and the boundary are set aside: a compact subgroup acts on a second-countable piece of the
manifold through a second-countable quotient, where $p$-adic exclusion applies; Newman's theorem
makes the kernel of that action independent of the piece, hence trivial; and the absence of small
subgroups passes from a compact normal subgroup and a Lie quotient to the whole group.

*Compact subgroups.* Fix a compact subgroup $K$ of the acting group $G$. The exhaustion that opens
Section 8 (see [where second countability goes](second-countability.md)) produces an open
submanifold $U$ that is nonempty, connected, second countable and $K$-invariant ([HS paper, lines 1369-1371](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L1369-L1371)).
Write $N_U$ for the subgroup of $K$ that fixes $U$ pointwise. The quotient $K/N_U$ acts faithfully
on $U$, so it injects into the metrizable group $\mathrm{Homeo}(U)$, and a compact metrizable group
is second countable. For such groups the paper cites the compact form of the reduction from Pardon
and combines it with the HS paper's Theorem 1.1 ($p$-adic exclusion), so $K/N_U$ is Lie ([HS paper, lines 1372-1375](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L1372-L1375)).
The logic is that of the classical reduction as the preprint quotes it: a non-Lie group with a
faithful action would contain a copy of $\mathbb{Z}_p$ ([preprint, §6, lines 519-522](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Hilbert-Smith-conjecture-in-every-finite-dimension-September-23-2026/build/sections/06-character-classes.tex#L519-L522)),
and the HS paper's Theorem 1.1 forbids a faithful action of that copy on $U$.

To see that $N_U$ is trivial, compare two such pieces $U \subset V$. The quotient $N_U/N_V$ is a
closed subgroup of the compact Lie group $K/N_V$, hence a compact Lie group, and it acts trivially on
the open set $U$ of the connected manifold $V$. Newman's theorem, in the form for compact Lie groups
cited from Pardon (such a group that fixes a nonempty open set pointwise acts trivially), gives
$N_U = N_V$ ([HS paper, lines 1376-1378](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L1376-L1378)). The exhaustion can start from $U$ and
absorb any given point, so every point lies in such a $V$; hence $N_U$ fixes the whole manifold and,
by effectivity, is trivial, and $K$ is Lie ([HS paper, lines 1379-1381](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L1379-L1381)).

*The whole group.* A Lie group has an identity neighbourhood that contains no subgroup except the
trivial one, and by Gleason–Yamabe this property (no small subgroups) characterizes Lie groups
among locally compact groups. Gleason–Yamabe also supplies an open subgroup $G_0 \subset G$ that is
an extension of a Lie group by a compact normal subgroup $K$. Both $K$, Lie by the first half, and
$G_0/K$ have no small subgroups, and the property passes to $G_0$. Take an identity neighbourhood of
$G_0$ that maps into a subgroup-free neighbourhood of $G_0/K$ and meets $K$ in a subgroup-free set. A
subgroup inside it has trivial image in $G_0/K$, so it lies in $K$, so it is trivial. As $G_0$ is
open in $G$, the group $G$ has no small subgroups and is Lie in its original topology ([HS paper, lines 1383-1390](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L1383-L1390)).

## OpenAI's proof

The proof of Theorem 1.1 is one paragraph ([preprint, §6, lines 518-527](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Hilbert-Smith-conjecture-in-every-finite-dimension-September-23-2026/build/sections/06-character-classes.tex#L518-L527)).
The idea is the classical reduction, quoted from the introduction of Pardon's paper on
three-manifolds: inside any non-Lie locally compact group with a faithful continuous action on a
connected manifold sits a closed subgroup isomorphic to some $\mathbb{Z}_p$. Given that, Theorem 1.2
finishes at once, because restricting an action to a subgroup keeps it jointly continuous and
faithful on the same manifold.

The introduction places the reduction in history ([preprint, §1, lines 59-74](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Hilbert-Smith-conjecture-in-every-finite-dimension-September-23-2026/build/sections/01-introduction.tex#L59-L74)).
It combines the structure theory of Gleason, Montgomery–Zippin and Yamabe with rigidity of
periodic transformations; Lee treats it, and Pardon states the form for actions used. The preprint
hands its second-countability hypothesis on the group to the cited reduction, without saying
whether the reduction needs it ([preprint, §6, lines 523-524](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Hilbert-Smith-conjecture-in-every-finite-dimension-September-23-2026/build/sections/06-character-classes.tex#L523-L524)). Its own explicit use of Newman's theorem is in the chart step ([preprint, Proposition 5.1](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Hilbert-Smith-conjecture-in-every-finite-dimension-September-23-2026/build/sections/05-local-tests.tex#L23-L50)).

## Side by side

|  | HS_proof | OpenAI's proof |
| --- | --- | --- |
| Idea | Compact subgroups first: on an invariant second-countable piece the compact quotient is Lie by the compact reduction and Theorem 1.1, and Newman's theorem kills the kernel; then Gleason–Yamabe structure gives no small subgroups | A non-Lie group acting faithfully contains an embedded $\mathbb{Z}_p$; restrict the action to it |
| Inputs | Compact $p$-adic reduction and Newman's theorem cited from Pardon, Gleason–Yamabe ([HS paper, lines 1374-1390](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L1374-L1390)); Theorem 1.1 | The classical reduction, cited from Pardon's three-manifold paper ([preprint, §6, lines 519-522](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Hilbert-Smith-conjecture-in-every-finite-dimension-September-23-2026/build/sections/06-character-classes.tex#L519-L522)); Theorem 1.2 |
| Formal status | proved in HS_proof by a different argument, second-countable case: no small subgroups, from prime-order Newman and Tao's Lemma 7 (a nontrivial compact, second-countable group with no nontrivial elements of finite order contains a copy of $\mathbb{Z}_p$), then Gleason–Yamabe. Without countability: proved here (Track A), by a third argument, for groups and manifolds in `Type` | not formalized on OpenAI's route. The bridge derives Theorem 1.1 from Theorem 1.2 with HS_proof's argument, for groups and manifolds in `Type` |
| Lean | [`HSFormal.hilbertSmith_of_padicExclusion'`](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSFormal/WeakInputs.lean#L175), [`HSFormal.Newman.newmanPrimeOrder`](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSFormal/Newman/Newman.lean#L14), [`HSGeneral.hilbertSmithNoSC_of_padicExclusion`](https://github.com/Deicyde/hilbert-smith/blob/1505120556bbe2ba3c6d4e77a0c3b0365da32abd/src/HSGeneral/Group.lean#L245) | [`HSBridge.hilbertSmith_of_padicExclusion`](https://github.com/Deicyde/hilbert-smith/blob/1505120556bbe2ba3c6d4e77a0c3b0365da32abd/src/HSBridge/Statements.lean#L76) |

## What is shared

- The direction of the argument: a group that is not Lie, acting faithfully, yields a faithful
  continuous action of some $\mathbb{Z}_p$ on a connected manifold, which $p$-adic exclusion
  forbids ([HS paper, lines 1374-1375](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L1374-L1375); [preprint, §6, lines 519-526](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Hilbert-Smith-conjecture-in-every-finite-dimension-September-23-2026/build/sections/06-character-classes.tex#L519-L526)).
- The ingredients: the Gleason–Yamabe structure theory of locally compact groups and rigidity of
  periodic maps in Newman's sense ([HS paper, lines 100-101](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L100-L101); [preprint, §1, lines 62-72](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Hilbert-Smith-conjecture-in-every-finite-dimension-September-23-2026/build/sections/01-introduction.tex#L62-L72)).
- Neither paper proves the group-theoretic core: the HS paper cites the compact $p$-adic
  reduction ([HS paper, lines 1374-1375](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L1374-L1375)),
  and the preprint cites the whole reduction ([preprint, §6, lines 519-522](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Hilbert-Smith-conjecture-in-every-finite-dimension-September-23-2026/build/sections/06-character-classes.tex#L519-L522)).

## What differs

- **How much is written out.** The HS paper cites the reduction only for compact groups and
  writes out the rest: the invariant second-countable pieces, the kernel argument and the
  Gleason–Yamabe assembly ([HS paper, lines 1369-1390](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L1369-L1390)).
  The preprint cites all of it.
- **Countability of the group.** The HS paper's group need not be second countable. It works with
  compact subgroups, where compactness of $K$ and metrizability of $\mathrm{Homeo}(U)$ make each
  compact quotient second countable before the cited reduction is applied ([HS paper, lines 1372-1375](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L1372-L1375)).
  The preprint assumes its group second countable ([preprint, Theorem 1.1](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Hilbert-Smith-conjecture-in-every-finite-dimension-September-23-2026/build/sections/01-introduction.tex#L9-L14))
  and passes the hypothesis to the cited reduction ([preprint, §6, lines 523-524](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Hilbert-Smith-conjecture-in-every-finite-dimension-September-23-2026/build/sections/06-character-classes.tex#L523-L524)),
  without saying whether the reduction needs it.
- **Newman's theorem.** The HS paper uses it explicitly once, to show that the kernel $N_U$ does
  not depend on $U$ ([HS paper, lines 1377-1378](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L1377-L1378)).
  The preprint's group step uses it nowhere explicitly; the preprint uses it in
  [the chart step](one-chart.md) instead.
- **Boundary and dimension.** The HS paper handles the point and the boundary first ([HS paper, line 1368](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L1368));
  the preprint's Theorem 1.1 is stated without boundary and for $n \geq 1$, with dimension $0$ in
  a remark ([preprint, §1, lines 16-20](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Hilbert-Smith-conjecture-in-every-finite-dimension-September-23-2026/build/sections/01-introduction.tex#L16-L20)).

## Read further

- In this book: [Classical reduction](../background/classical-reduction.md),
  [Newman rigidity](../background/newman-rigidity.md),
  [Hilbert–Smith conjecture](../main-theorem/hilbert-smith-conjecture.md).
- In this chapter: [Where second countability goes](second-countability.md),
  [The theorems without second countability](general-case.md),
  [What each paper proves](statements.md).
- In HSWiki: [From p-adic exclusion to Hilbert–Smith](https://deicyde.github.io/hs-proof-wiki/roadmap/reduction/index.html),
  [Hilbert–Smith from p-adic exclusion](https://deicyde.github.io/hs-proof-wiki/roadmap/reduction/index.html#hilbert-smith-from-padic-exclusion),
  [Newman's theorem for prime-order homeomorphisms](https://deicyde.github.io/hs-proof-wiki/roadmap/reduction/index.html#newman-prime-order),
  [Compact torsion-free groups contain a p-adic integer group](https://deicyde.github.io/hs-proof-wiki/roadmap/reduction/index.html#compact-torsion-free-contains-padic),
  [No small subgroups implies Lie](https://deicyde.github.io/hs-proof-wiki/roadmap/reduction/index.html#nss-is-lie).

## Sources

- [HS paper, lines 100-101: the standard reduction](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L100-L101)
- [HS paper, lines 1367-1391: proof of Corollary 1.2](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L1367-L1391)
- [HS paper, lines 1439-1445: Pardon's two-manifold paper, the cited source](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L1439-L1445)
- [Preprint, §1, lines 59-74: the reduction in history](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Hilbert-Smith-conjecture-in-every-finite-dimension-September-23-2026/build/sections/01-introduction.tex#L59-L74)
- [Preprint, §6, lines 518-527: proof of Theorem 1.1](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Hilbert-Smith-conjecture-in-every-finite-dimension-September-23-2026/build/sections/06-character-classes.tex#L518-L527)
