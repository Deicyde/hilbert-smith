---
article_id: af_ff90309961b7f44d3d88969a
---

# What each paper proves

*What exactly does each paper prove, and do the two papers prove the same thing?*

Both papers open with two theorems, one about actions of the $p$-adic integers $\mathbb{Z}_p$ and
the Hilbert–Smith conjecture, and both prove the second from the first. The numbering is crossed:
the HS paper's Theorem 1.1 is $p$-adic exclusion and its Corollary 1.2 is Hilbert–Smith, while
the preprint's Theorem 1.1 is Hilbert–Smith and its Theorem 1.2 is $p$-adic exclusion. Most later
stages of this chapter serve the proof of $p$-adic exclusion; [the group reduction](groups-to-zp.md)
turns it into Hilbert–Smith.

## HS_proof

In the HS paper the theorem about $\mathbb{Z}_p$ comes first. Theorem 1.1, $p$-adic exclusion: for
no prime $p$ does $\mathbb{Z}_p$ act faithfully and continuously on a connected manifold of finite
dimension; some nonzero element always acts trivially ([HS paper, lines 85-88](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L85-L88)).
Corollary 1.2, Hilbert–Smith: a locally compact Hausdorff group with a faithful continuous action on
such a manifold carries a Lie group structure compatible with its own topology ([HS paper, lines 90-94](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L90-L94)).
The conventions are generous ([HS paper, lines 96-97](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L96-L97) and [line 129](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L129)):

- a manifold is a topological Hausdorff manifold, and boundary is allowed;
- a Lie group may have any number of components;
- actions are jointly continuous;
- nothing is assumed countable, neither the manifold nor the group.

The proof of Theorem 1.1 first clears away two special cases ([HS paper, lines 1352-1359](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L1352-L1359)).
A connected manifold of dimension $0$ is a point, on which all of $\mathbb{Z}_p$ is the kernel. If
there is boundary, pass to the interior: it is dense and connected, local homology tells interior
points from boundary points so that every homeomorphism maps the interior to itself, and by density
an element trivial on the interior is trivial everywhere. So effectivity survives, and the interior
has no boundary. In the boundaryless case the paper pits two results against each other:
Proposition 13.1 turns an effective action into a class with tail signature $1$, and the
divisibility theorem, Theorem 4.3, forces that tail to be eventually divisible by $p$, so
$1 \in p\mathbb{Z}$ ([HS paper, lines 1361-1364](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L1361-L1364)).
The introduction calls the obstruction an integer signature tail ([HS paper, lines 103-120](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L103-L120)).
It also stresses that everything happens inside a single coordinate chart, so the manifold never
needs a global orientation or triangulation ([HS paper, lines 97-99](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L97-L99)).

## OpenAI's proof

The preprint's Theorem 1.1 is Hilbert–Smith in positive dimension. Take $n \geq 1$, a topological
$n$-manifold without boundary that is connected, Hausdorff and second countable, and a group that is
locally compact, Hausdorff and second countable, acting on it faithfully and jointly continuously;
then the group is Lie ([preprint, Theorem 1.1](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Hilbert-Smith-conjecture-in-every-finite-dimension-September-23-2026/build/sections/01-introduction.tex#L9-L14)).
Nothing is asked of the manifold beyond this (no compactness, orientability or triangulation), and
stabilizers may be anything. Dimension $0$, which the theorem leaves out, is trivial: the manifold
is a point, only the trivial group acts on it faithfully, and the conclusion holds ([preprint, §1, lines 16-20](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Hilbert-Smith-conjecture-in-every-finite-dimension-September-23-2026/build/sections/01-introduction.tex#L16-L20)).
Theorem 1.2 is $p$-adic exclusion on the same manifolds, again with $n \geq 1$: no jointly
continuous action of $\mathbb{Z}_p$ is faithful, and in fact each one factors through some finite
quotient $\mathbb{Z}/p^j$ ([preprint, Theorem 1.2](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Hilbert-Smith-conjecture-in-every-finite-dimension-September-23-2026/build/sections/01-introduction.tex#L30-L35)).
Joint continuity means continuity of the homomorphism $\mathbb{Z}_p \to \mathrm{Homeo}(M)$ for the
compact-open topology ([preprint, §1, lines 37-40](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Hilbert-Smith-conjecture-in-every-finite-dimension-September-23-2026/build/sections/01-introduction.tex#L37-L40)).

Theorem 1.2 is proved at the very end. Proposition 5.1 shrinks a faithful action to an open
subgroup, again a copy of $\mathbb{Z}_p$, that acts faithfully and preserves orientation on a
connected invariant open set $O$ of one chart, viewed inside $\mathbb{R}^n$, and Theorem 6.8 rules that out
([preprint, §6, lines 502-507](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Hilbert-Smith-conjecture-in-every-finite-dimension-September-23-2026/build/sections/06-character-classes.tex#L502-L507)).
The finite-quotient clause is one more step: the kernel is closed, as the intersection of the
closed point stabilizers, and a nonzero closed subgroup of $\mathbb{Z}_p$ contains some
$p^j\mathbb{Z}_p$, so it is open ([preprint, §6, lines 507-512](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Hilbert-Smith-conjecture-in-every-finite-dimension-September-23-2026/build/sections/06-character-classes.tex#L507-L512)).
The engine of Theorem 6.8 is arithmetic: for every $k$ a faithful action gives $p^k$ integral
classes in a Witt group $E_d(S^d)$ of sheaf complexes on the sphere, whose rational part is a line
spanned by the orientation class $\overline{u}_d$; their rational images are equal and sum to
$4\overline{u}_d$, while every integral class lies in a fixed lattice $L_d^{-1}\mathbb{Z}\overline{u}_d$,
with $L_d$ a power of $2$ chosen before $k$; that fails once $p^k > 4L_d$ ([preprint, §1, lines 165-181](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Hilbert-Smith-conjecture-in-every-finite-dimension-September-23-2026/build/sections/01-introduction.tex#L165-L181)).
Theorem 1.1 follows from Theorem 1.2 by a cited reduction ([preprint, §6, lines 518-527](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Hilbert-Smith-conjecture-in-every-finite-dimension-September-23-2026/build/sections/06-character-classes.tex#L518-L527)).
The preprint also records a corollary: some positive iterate of an almost-periodic homeomorphism is
the time-one map of a continuous flow ([preprint, §1, lines 42-55](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Hilbert-Smith-conjecture-in-every-finite-dimension-September-23-2026/build/sections/01-introduction.tex#L42-L55)).

## Side by side

|  | HS_proof | OpenAI's proof |
| --- | --- | --- |
| Idea | An effective action gives a degree-four class whose signatures are eventually $1$; divisibility over a free $C_p$-space makes them eventually divisible by $p$ | A faithful action gives $p^k$ equal integral classes summing to $4\overline{u}_d$ in a group whose integral classes lie in a fixed lattice $L_d^{-1}\mathbb{Z}\overline{u}_d$ |
| Inputs | Ultimate lower quadratic $L$-theory with Karoubi localization ([HS paper, lines 140-147](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L140-L147)); for Corollary 1.2, the compact $p$-adic reduction and Newman's theorem cited from Pardon, and Gleason–Yamabe | Verdier duality, Balmer's Witt groups and Balmer–Walter localization ([preprint, §1, lines 132-140](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Hilbert-Smith-conjecture-in-every-finite-dimension-September-23-2026/build/sections/01-introduction.tex#L132-L140)); Newman's theorem; for Theorem 1.1, the classical reduction |
| Formal status | proved in HS_proof, second-countable case, boundary forms included; comparator checks `hilbert_smith` and the two Formal Conjectures second-countable variants, not the boundary forms. Without countability: proved here (Track A) | Theorem 1.2: proved here from the interface (`δD`, `inv`, `chars`) and Newman's theorem (`NewmanInput`), with Lemmas 5.4 and 5.5 assumed (OrbitNull), and a build check that the proof uses no HS_proof constant; without second countability, from the same interface fields and OrbitNull alone, Newman's theorem being derived from HS_proof's proof of it. Its Lean statement copies HS_proof's binders on purpose and equals HS_proof's by definition, checked against neither paper. Theorem 1.1, the finite-quotient clause and the corollary: not formalized on OpenAI's route |
| Lean | [`HSFormal.Universe.padicExclusion_univ`](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSFormal/Universe.lean#L279), [`HSFormal.hilbertSmith`](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSFormal/HilbertSmithNegK.lean#L36), [`HSFormal.hilbertSmith_all`](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSFormal/HilbertSmithNegK.lean#L30) | [`HSBridge.oai_route`](https://github.com/Deicyde/hilbert-smith/blob/1505120556bbe2ba3c6d4e77a0c3b0365da32abd/src/HSBridge/SideBySide.lean#L132), [`HSBridge.oai_route_noSC`](https://github.com/Deicyde/hilbert-smith/blob/1505120556bbe2ba3c6d4e77a0c3b0365da32abd/src/HSBridge/SideBySide.lean#L140), [`HSBridge.statements_agree`](https://github.com/Deicyde/hilbert-smith/blob/1505120556bbe2ba3c6d4e77a0c3b0365da32abd/src/HSBridge/Statements.lean#L44) |

## What is shared

- Both reach Hilbert–Smith through $p$-adic exclusion: a group that is not Lie would give a
  faithful continuous action of some $\mathbb{Z}_p$ ([HS paper, lines 100-101](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L100-L101); [preprint, §1, lines 22-28](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Hilbert-Smith-conjecture-in-every-finite-dimension-September-23-2026/build/sections/01-introduction.tex#L22-L28)).
- Both prove $p$-adic exclusion by contradiction from a faithful action, inside one coordinate
  chart, with no global orientation or triangulation of the manifold ([HS paper, lines 97-99](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L97-L99); [preprint, §6, lines 502-515](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Hilbert-Smith-conjecture-in-every-finite-dimension-September-23-2026/build/sections/06-character-classes.tex#L502-L515)).
- On connected, Hausdorff, second-countable manifolds of positive dimension without boundary, the
  two $p$-adic statements say the same thing, "nontrivial kernel" in one and "nonzero kernel" in
  the other; the Hilbert–Smith statements agree likewise for second-countable groups.
  [The two statements agree](same-statement.md) states the comparison precisely.

## What differs

- **Countability.** The HS paper assumes none, on the manifold or on the group; the preprint
  assumes both second countable ([preprint, §1, lines 10-12](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Hilbert-Smith-conjecture-in-every-finite-dimension-September-23-2026/build/sections/01-introduction.tex#L10-L12) and [line 32](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Hilbert-Smith-conjecture-in-every-finite-dimension-September-23-2026/build/sections/01-introduction.tex#L32)).
  See [where second countability goes](second-countability.md).
- **Boundary.** The HS paper allows it and passes to the interior ([HS paper, lines 1353-1359](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L1353-L1359));
  the preprint states only manifolds without boundary.
- **Dimension $0$.** The HS paper's Theorem 1.1 covers it, as the case of a point ([HS paper, line 1353](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L1353)).
  The preprint's Theorem 1.2 assumes $n \geq 1$, and its remark on dimension $0$ concerns
  Theorem 1.1 only ([preprint, §1, lines 18-20](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Hilbert-Smith-conjecture-in-every-finite-dimension-September-23-2026/build/sections/01-introduction.tex#L18-L20)).
- **Extras.** The preprint adds the finite-quotient clause to Theorem 1.2 and the almost-periodic
  corollary; the HS paper states neither.
- **The collision.** The HS paper ends with $1 \in p\mathbb{Z}$; the preprint ends with
  $0 < 4L_d/p^k < 1$, against integrality ([preprint, §6, lines 496-498](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Hilbert-Smith-conjecture-in-every-finite-dimension-September-23-2026/build/sections/06-character-classes.tex#L496-L498)).
  See [the collision](contradiction.md).

## Read further

- In this book: [Main theorems](../main-theorem/README.md),
  [$p$-adic exclusion](../main-theorem/padic-exclusion.md),
  [Hilbert–Smith conjecture](../main-theorem/hilbert-smith-conjecture.md),
  [Almost-periodic flow](../main-theorem/almost-periodic-flow.md).
- In this chapter: [The two statements agree](same-statement.md),
  [The theorems without second countability](general-case.md),
  [From locally compact groups to $\mathbb{Z}_p$](groups-to-zp.md).
- In HSWiki: [p-adic exclusion](https://deicyde.github.io/hs-proof-wiki/roadmap/main-theorems/index.html#padic-exclusion),
  [The Hilbert–Smith conjecture](https://deicyde.github.io/hs-proof-wiki/roadmap/main-theorems/index.html#hilbert-smith),
  [Manifolds with boundary](https://deicyde.github.io/hs-proof-wiki/roadmap/main-theorems/index.html#boundary-forms).

## Sources

- [HS paper, lines 85-101: Theorem 1.1, Corollary 1.2 and conventions](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L85-L101)
- [HS paper, lines 103-120: the obstruction](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L103-L120)
- [HS paper, lines 1352-1365: proof of Theorem 1.1](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L1352-L1365)
- [Preprint, §1, lines 9-55: Theorems 1.1 and 1.2, dimension zero, the corollary](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Hilbert-Smith-conjecture-in-every-finite-dimension-September-23-2026/build/sections/01-introduction.tex#L9-L55)
- [Preprint, §1, lines 165-181: equal parts in a fixed lattice](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Hilbert-Smith-conjecture-in-every-finite-dimension-September-23-2026/build/sections/01-introduction.tex#L165-L181)
- [Preprint, §6, lines 496-527: the contradiction and the proofs of Theorems 1.2 and 1.1](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Hilbert-Smith-conjecture-in-every-finite-dimension-September-23-2026/build/sections/06-character-classes.tex#L496-L527)
