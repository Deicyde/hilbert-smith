---
article_id: af_c5e165a49d97c8b3aef6e1cf
declaration: theorem
origin: bridged
lean: HSBridge.statements_agree HSBridge.hilbertSmith_statements_agree
statement: formalized
proof: formalized
---

# The two statements agree

Here a topological $n$-manifold, for any $n \geq 0$, is a Hausdorff space with an atlas of charts,
for its own topology, onto open subsets of $\mathbb{R}^n$; it has no boundary, and no
differentiable structure is assumed. A topological group is a Lie group if, for some $d$, its own
topology carries a $C^\infty$ atlas (charts with smooth transition maps) modelled on
$\mathbb{R}^d$, in which multiplication and inversion are $C^\infty$. Consider two propositions.

- *$p$-adic exclusion*: for every prime $p$, every $n \geq 0$ and every connected, Hausdorff,
  second-countable topological $n$-manifold $M$, no jointly continuous action of $\mathbb{Z}_p$ on
  $M$ is faithful; that is, some nonzero element of $\mathbb{Z}_p$ acts as the identity.
- *Hilbert–Smith*: for every $n \geq 0$, every such $M$, and every locally compact, Hausdorff,
  second-countable topological group $G$ acting jointly continuously and faithfully on $M$ (only
  the identity fixes every point), $G$ is a Lie group.

Each proposition is stated in both papers: $p$-adic exclusion as the preprint's Theorem 1.2 and
the HS paper's Theorem 1.1, Hilbert–Smith as the preprint's Theorem 1.1 and the HS paper's
Corollary 1.2. Read for second-countable manifolds without boundary and second-countable groups,
with $n = 0$ admitted and without the preprint's finite-quotient clause, the two formulations in
each pair both state the corresponding proposition above, so they are equivalent.

The comparison is narrow. Both propositions allow $n = 0$, where $M$ is a point and both hold
trivially, whereas the preprint's two theorems assume $n \geq 1$. Neither records the preprint's
clause that the action factors through a finite quotient of $\mathbb{Z}_p$, and neither covers the
HS paper's manifolds with boundary or without second countability (for the latter, see
[The theorems without second countability](general-case.md)).
[What each paper proves](statements.md) compares the full statements.

*Proof sketch.* In each pair the two formulations quantify over the same data, impose the same
hypotheses and draw the same conclusion, so each is the other.

## Sources

- [HS paper, lines 85-97: Theorem 1.1, Corollary 1.2 and conventions](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L85-L97)
- [Preprint, §1, lines 9-35: Theorems 1.1 and 1.2, and dimension zero](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Hilbert-Smith-conjecture-in-every-finite-dimension-September-23-2026/build/sections/01-introduction.tex#L9-L35)
- [Preprint source map: `cor:lie`, `thm:main`](../../sources/preprint.md)

## Depends on

This node has no prerequisites.
