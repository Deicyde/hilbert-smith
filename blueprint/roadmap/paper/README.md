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
3. *Construction and two computations.* From the local data a later
   chapter builds a controlled Poincaré complex over $T\times S^n$
   (Theorem C). Its tail of signatures is eventually $\pm 1$
   (Theorem B, evaluation) and eventually divisible by $p$ (Theorem A,
   divisibility), and no integer sequence does both. This proves
   $p$-adic exclusion without boundary; the boundary case passes to the
   intrinsic interior.
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
text uses them.

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

- [Local data from a faithful action](local-data/README.md)
- [The main theorems](proofs/README.md)
- [Appendices: the cited inputs](inputs/README.md)
