---
article_id: af_0863521ecc3d50e2d53ff2ce
published: false
---

# The Hilbert–Smith conjecture in one paper

This paper proves two theorems along a single route. Throughout, an
$n$-manifold is a Hausdorff space with an atlas of charts, each a
homeomorphism from an open subset onto an open subset of
$\mathbb{R}^n$; a manifold with boundary uses the half-space
$\{x\in\mathbb{R}^n : x_0\ge 0\}$ in place of $\mathbb{R}^n$. No
countability is assumed, and connected spaces are nonempty.

**Theorem ($p$-adic exclusion).** Let $p$ be a prime and let $M$ be a
connected manifold, with or without boundary. No continuous action of
the $p$-adic integers $\mathbb{Z}_p$ on $M$ is faithful: some nonzero
element of $\mathbb{Z}_p$ fixes every point of $M$.

**Theorem (Hilbert–Smith).** A locally compact group that acts
continuously and faithfully on a connected manifold, with or without
boundary, is a Lie group, for its given topology. The group is not
assumed Hausdorff or second countable.

## The plan

The proof has four steps.

1. *One chart.* Given a faithful action of $\mathbb{Z}_p$, Newman's
   theorem gives a good point: no open subgroup $p^j\mathbb{Z}_p$ fixes
   any neighbourhood of it pointwise. Saturating a small coordinate
   ball at that point gives a connected open set $O\subseteq\mathbb{R}^n$
   on which a copy of $\mathbb{Z}_p$ acts faithfully. Second
   countability is never needed, because $O$ lies in $\mathbb{R}^n$.
2. *Local data.* On such a set we average the chart over the group,
   cut out a compact invariant test region on which no point is fixed
   by the whole group, pinch a sphere onto it by a map homotopic to the
   identity, and pass to the orbit space of the test region under the
   subgroup $p\mathbb{Z}_p$. With the orbit metric this orbit space is
   a compact metric space $T$ carrying a free isometric action of the
   cyclic group $C_p$.
3. *Construction and two computations.* When the control space is
   nonempty, it and the groups $G_i=\mathbb Z/p^i$ form the standing
   data of the corner chapter. Theorem C (compression) compresses the labelled chain
   models of the torus form of the test map into a strict Poincaré
   complex over $T\times S^n$ with a graph-type homotopy action of the
   $G_i$, whose image after forgetting $T$ is the class of the torus
   test map. Theorem A (corner) shows that for every such complex the
   tail signature of the iterated cut is eventually divisible by $p$;
   its arithmetic core is the divisibility theorem for classes over a
   free $C_p$-space. Theorem B (evaluation) shows that the iterated cut
   of the class of any labelling homotopic to the cubical pinch has
   tail signature eventually equal to a constant $\pm1$, and the torus
   test map is such a labelling. No integer sequence is eventually
   both $\pm1$ and divisible by $p$; and if the control space is
   empty, the compressed complex is zero, so the tail is zero. This proves $p$-adic exclusion
   without boundary; the boundary case passes to the intrinsic
   interior.
4. *Groups.* Let a locally compact group act faithfully. Newman's
   theorem on small orbits rules out elements of prime order in the
   closure of any subgroup inside a small compact neighbourhood of the
   identity. That closure is then compact and torsion-free, and if it
   were nontrivial it would contain a copy of $\mathbb{Z}_p$, which
   step 3 forbids. So the group has no small subgroups, and the
   Gleason–Yamabe theorem makes it a Lie group.

Three results are cited rather than proved: Newman's theorem in two
forms, the embedding of $\mathbb{Z}_p$ in a compact torsion-free group
(whose proof through Pontryagin duality the appendices sketch), and the
Gleason–Yamabe theorem. The appendices state them exactly as the main
text uses them, as open statements: theorems that the Lean states now
and proves later. A few statements inside the chapters are open in the
same sense: lifting, the two sides of an excision boundary and Lemma U
in the L-theory chapter, and the splitting of idempotents in the
bounded homotopy category used by the corner chapter. Both main
theorems rest on all of these until they are proved.

## Attribution

The architecture is that of the HS paper: signature tails over a free
$C_p$-space, divisibility played against evaluation, the reduction from
manifolds with boundary to their interiors, and the passage from groups
to $\mathbb{Z}_p$ (see the [HS paper, Section 1](../../sources/hs-paper.md#section-1-introduction-secintroduction-lines-76-150)
and [Section 13](../../sources/hs-paper.md#section-13-the-contradiction-seccontradiction-lines-1326-1391)).
The good point, the one-chart reduction and the orbit metric come from
the OpenAI preprint (see the [OpenAI preprint, Section 5](../../sources/preprint.md#section-5-local-tests-sections05-local-teststex),
05-local-tests.tex lines 14-73 and 117-131). The group step through
Newman's theorem on small orbits follows the classical reduction rather
than either paper's text.

## Sources

- [HS paper, Section 1](../../sources/hs-paper.md#section-1-introduction-secintroduction-lines-76-150)
- [OpenAI preprint, Section 1](../../sources/preprint.md#section-1-introduction-sections01-introductiontex), 01-introduction.tex lines 9-74

## Chapters

In reading order:

- [Algebraic L-theory](l-theory/README.md): L-groups of strict symmetric Poincaré complexes over any category with strict duality, their bounded and ultimate lower versions, and the localization boundary with its exactness.
- [Asymptotic controlled categories](categories/README.md): categories of sequences of free $G_i$-modules labelled in a compact metric space, with propagation tending to zero, their support subcategories and exterior quotients, the functors between them, and the cut boundary.
- [Integer signatures and tails](signatures/README.md): equivariant signatures of 4-dimensional Poincaré complexes over $\mathbb Q[G]$ and the tail signature $\sigma_{\mathrm{tail}}$, a class of integer sequences modulo finitely supported ones.
- [Divisibility over a free $C_p$-space](divisibility/README.md): the [divisibility theorem](divisibility/divisibility.md), that the tail signature of every class over a free isometric $C_p$-space is eventually divisible by $p$.
- [The graph corner](corner/README.md): the standing data and [Theorem A](corner/theorem/theorem-a.md), turning a Poincaré complex over $T\times S^n$ with a graph-type homotopy action into a class over $T$, so that its iterated cut has tail signature eventually divisible by $p$.
- [Local data from a faithful action](local-data/README.md): from a faithful action of $\mathbb Z_p$, a good point, a local datum on an open subset of $\mathbb R^n$, the test map, and the compact control space $T$ with its free isometric $C_p$-action.
- [Chain models](chain-models/README.md): the cubical chain models of $\mathbb T^n\times\mathbb{CP}^2$ with their Poincaré structure, and chain approximations of the action with estimates in sphere labels.
- [Compression](compression/README.md): [Theorem C](compression/theorem-c.md), cutting the chain models down to the cells near the test region to get a Poincaré complex over $T\times S^n$ with a graph-type homotopy action, whose image after forgetting $T$ is the class of the torus test map.
- [Evaluation of the iterated cut](evaluation/README.md): [Theorem B](evaluation/theorem-b.md), that the iterated cut of the class of a labelling homotopic to the cubical pinch has tail signature eventually $\pm1$, and its [form for the test map](evaluation/theorem-b-test-map.md).
- [The main theorems](proofs/README.md): the reduction to one chart, local exclusion from Theorems A, B and C, the boundary case, and Hilbert–Smith through the absence of small subgroups.
- [Appendices: the cited inputs](inputs/README.md): Newman's theorem, $\mathbb Z_p$ in compact torsion-free groups, and the Gleason–Yamabe theorem, stated as open statements.
