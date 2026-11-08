---
article_id: af_b5fba1a073397fac914a7ad9
declaration: theorem
origin: bridged
lean: HSGeneral.padicExclusionNoSC HSGeneral.hilbertSmithNoSC HSBridge.generalCase_hs HSBridge.generalCase_oai
statement: formalized
proof: formalized
---

# The theorems without second countability

Here a topological $n$-manifold, for any $n \geq 0$, is a Hausdorff space with an atlas of charts,
for its own topology, onto open subsets of $\mathbb{R}^n$; it has no boundary, and no countability
is assumed.

1. *$p$-adic exclusion.* For every prime $p$, every $n \geq 0$ and every connected topological
   $n$-manifold $M$, in any universe, no jointly continuous action of $\mathbb{Z}_p$ on $M$ is
   faithful: some nonzero element of $\mathbb{Z}_p$ acts as the identity.
2. *Hilbert–Smith.* Let $M$ be a connected topological $n$-manifold and $G$ a locally compact
   topological group, both in the lowest universe, `Type`, with $G$ acting jointly continuously
   and faithfully on $M$. Then $G$ is a Lie group: for some $d$, its own topology carries an atlas
   modelled on $\mathbb{R}^d$ in which multiplication and inversion are $C^\infty$. Neither $M$
   nor $G$ is assumed second countable, and $G$ is not assumed Hausdorff.

These are the HS paper's Theorem 1.1 and Corollary 1.2 for manifolds without boundary, with no
countability, as the paper states them ([HS paper, lines 85-97](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L85-L97));
the paper assumes the group Hausdorff, which here follows from faithfulness on a Hausdorff space.
The preprint states both theorems with second countability and $n \geq 1$
([preprint, §1, lines 9-35](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Hilbert-Smith-conjecture-in-every-finite-dimension-September-23-2026/build/sections/01-introduction.tex#L9-L35)).
Part 2 covers groups and manifolds in `Type` only; Formal Conjectures' form of Hilbert–Smith, in
any universe and with a real-analytic conclusion, is not proved.

*Proof sketch.* Both parts are derived from HS_proof's theorems for second-countable manifolds.
Part 1 is derived in two ways, one for each paper's reduction to the second-countable case; only
the reductions differ, and both ways end in the same second-countable theorem.

- *The HS paper's reduction.* A faithful action moves, for each $j$, some point $x_j$ by $p^j$.
  Because $\mathbb{Z}_p$ is compact, an exhaustion by relatively compact connected open sets, each
  containing the orbit of the closure of the one before, gives a connected, second-countable,
  invariant open set $U$ containing every $x_j$ ([HS paper, lines 757-768](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L757-L768)).
  The kernel on $U$ is a closed subgroup of $\mathbb{Z}_p$; a nonzero one would be some
  $p^m\mathbb{Z}_p$, but $p^m$ moves $x_m$. So $\mathbb{Z}_p$ acts faithfully on the
  second-countable manifold $U$, against the second-countable theorem. Newman's theorem is not
  used.
- *OpenAI's reduction.* The argument of Proposition 5.1, without its orientation step, turns a
  faithful action on $M$ into a faithful action of $\mathbb{Z}_p$ on a connected open subset $O$
  of $\mathbb{R}^n$, using Newman's theorem ([preprint, §5, lines 23-66](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Hilbert-Smith-conjecture-in-every-finite-dimension-September-23-2026/build/sections/05-local-tests.tex#L23-L66)).
  As a subspace of $\mathbb{R}^n$, $O$ is second countable, and one chart makes it an
  $n$-manifold, against the second-countable theorem in the lowest universe. Newman's theorem is
  taken from HS_proof's proof of it.
- *Hilbert–Smith.* Part 2 follows from second-countable $p$-adic exclusion by an argument that is
  neither paper's. A compact identity neighbourhood lies in an open subgroup $G_0$ that is a
  countable union of compact sets, and some connected, second-countable open set $V_0$ is
  $G_0$-invariant. The quotient of $G_0$ by its kernel on $V_0$ has no small subgroups, so the
  subgroups near the identity fix $V_0$ pointwise. The closure $K$ of such a subgroup is compact;
  the same construction applied to $K$ gives a compact, second-countable quotient acting
  faithfully on a second-countable manifold, which is torsion-free by Newman's theorem and, if
  nontrivial, contains a copy of $\mathbb{Z}_p$ by Tao's Lemma 7 (a nontrivial compact,
  second-countable group with no nontrivial elements of finite order contains a copy of
  $\mathbb{Z}_p$), against $p$-adic exclusion. So
  $G$ has no small subgroups, and the Gleason–Yamabe theorem, which needs no second countability,
  makes it a Lie group.

## Sources

- [HS paper, lines 85-97: Theorem 1.1, Corollary 1.2 and conventions](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L85-L97)
- [HS paper, lines 757-768: the invariant second-countable submanifold](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L757-L768)
- [HS paper, lines 1367-1391: proof of Corollary 1.2](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L1367-L1391)
- [Preprint, §5, lines 14-73: Proposition 5.1](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Hilbert-Smith-conjecture-in-every-finite-dimension-September-23-2026/build/sections/05-local-tests.tex#L14-L73)
- [Preprint source map: `cor:lie`, `thm:main`, `prop:chart-reduction`](../../sources/preprint.md)
- [The two reductions, as compared here](https://github.com/Deicyde/hilbert-smith/blob/1505120556bbe2ba3c6d4e77a0c3b0365da32abd/src/HSBridge/GeneralCase.lean#L4-L80)
- [The group argument, as proved here](https://github.com/Deicyde/hilbert-smith/blob/1505120556bbe2ba3c6d4e77a0c3b0365da32abd/src/HSGeneral/Group.lean#L39-L58)

## Depends on

This node has no prerequisites.
