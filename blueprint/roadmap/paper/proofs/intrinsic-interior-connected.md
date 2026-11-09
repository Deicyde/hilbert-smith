---
article_id: af_82ec1e9cd20cf1c0cb585134
declaration: lemma
origin: bridged
---

# The intrinsic interior is connected

Let $n\ge1$ and let $M$ be a connected topological space with an atlas of charts onto open subsets of the half-space $\{x\in\mathbb{R}^n:x_0\ge0\}$. Then $M^\circ_n$ is connected.

*Proof sketch.*
1. Each point of $M$ has arbitrarily small neighbourhoods $V$ that a chart maps onto a relative half-ball $\{y : y_0\ge0,\ |y-c|<r\}$. The set $V\cap M^\circ_n$ contains the part over the open half-ball, which is convex, and lies in its closure, so $V\cap M^\circ_n$ is connected.
2. Suppose $M^\circ_n=A\sqcup B$ with $A,B$ open in $M^\circ_n$. Let $\hat A$ be the set of points of $M$ having such a $V$ with $V\cap M^\circ_n\subseteq A$, and $\hat B$ likewise. Both are open, and they cover $M$ by step 1.
3. They are disjoint: two such neighbourhoods of one point intersect in a nonempty open set, which meets $M^\circ_n$ by density, so the point cannot be in both.
4. $M$ is connected, so $\hat A$ or $\hat B$ is empty, and hence $A$ or $B$ is empty.

## Sources

- [HS paper, Section 13](../../../sources/hs-paper.md#section-13-the-contradiction-seccontradiction-lines-1326-1391) (proof of Theorem 1.1, dimension 0 and boundary)
- New: an argument by half-balls, in place of local homology

## Depends on

- [Intrinsic interior](intrinsic-interior.md)

## Proof depends on

- [The intrinsic interior is dense](intrinsic-interior-dense.md)
