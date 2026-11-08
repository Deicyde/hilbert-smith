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
topology carries an atlas modelled on $\mathbb{R}^d$ in which multiplication and inversion are
$C^\infty$. All manifolds and groups lie in the lowest universe, `Type`. Consider two
propositions.

- *$p$-adic exclusion*: for every prime $p$, every $n \geq 0$ and every connected, Hausdorff,
  second-countable topological $n$-manifold $M$, no jointly continuous action of $\mathbb{Z}_p$ on
  $M$ is faithful; that is, some nonzero element of $\mathbb{Z}_p$ acts as the identity.
- *Hilbert–Smith*: for every $n \geq 0$, every such $M$, and every locally compact, Hausdorff,
  second-countable topological group $G$ acting jointly continuously and faithfully on $M$ (only
  the identity fixes every point), $G$ is a Lie group.

Each proposition is written twice as a Lean definition: in this repository, from the preprint's
Theorem 1.2 and Theorem 1.1, and in HS_proof's library, for the second-countable boundaryless case
of the HS paper's Theorem 1.1 and Corollary 1.2. The two definitions of $p$-adic exclusion are
equivalent, and so are the two definitions of Hilbert–Smith: in each pair, one definition unfolds
to the other.

What this checks is narrow. The definitions in this repository were written with HS_proof's
hypotheses, in HS_proof's order, on purpose, so that each equivalence holds by reflexivity. It
compares two Lean definitions with each other and checks neither against its paper; that each
definition says what its paper says is a matter of reading, done in
[What each paper proves](statements.md). Both definitions allow $n = 0$, where $M$ is a point and
both statements hold trivially, whereas the preprint's Theorem 1.2 assumes $n \geq 1$. Neither
records the preprint's clause that the action factors through a finite quotient of
$\mathbb{Z}_p$, and neither covers the HS paper's manifolds with boundary or without second
countability (for those, see [The theorems without second countability](general-case.md)).

*Proof sketch.* In each pair the two definitions quantify over the same data with the same
hypotheses in the same order, and draw the same conclusion, so reflexivity (`Iff.rfl`) proves the
equivalence. The same comparison holds in every universe, against HS_proof's universe-polymorphic
forms of the two statements.

## Sources

- [HS paper, lines 85-97: Theorem 1.1, Corollary 1.2 and conventions](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L85-L97)
- [HS paper, lines 1398-1400: HS_proof's formalization, under second countability](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L1398-L1400)
- [Preprint, §1, lines 9-35: Theorems 1.1 and 1.2, and dimension zero](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Hilbert-Smith-conjecture-in-every-finite-dimension-September-23-2026/build/sections/01-introduction.tex#L9-L35)
- [Preprint source map: `cor:lie`, `thm:main`](../../sources/preprint.md)
- [The statements as written here, with the remark that their binders match HS_proof's](https://github.com/Deicyde/hilbert-smith/blob/1505120556bbe2ba3c6d4e77a0c3b0365da32abd/src/HilbertSmith/Statements.lean#L28-L84)

## Depends on

This node has no prerequisites.
