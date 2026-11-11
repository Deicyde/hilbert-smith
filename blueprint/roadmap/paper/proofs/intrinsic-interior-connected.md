---
article_id: af_82ec1e9cd20cf1c0cb585134
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.isConnected_intrinsicInterior
---

# The intrinsic interior is connected

Let $n\ge1$ and let $M$ be a connected topological space with an atlas of charts onto open subsets of the half-space $\{x\in\mathbb{R}^n:x_0\ge0\}$. Then $M^\circ_n$ is connected.

*Proof sketch.*
1. $M^\circ_n$ is nonempty, because it is dense in $M$ and $M$, being connected, is nonempty.
2. Each point of $M$ has a neighbourhood $V$ that a chart maps onto a relative half-ball $\{y : y_0\ge0,\ |y-c|<r\}$. The set $V\cap M^\circ_n$ contains the part over the open half-ball, since points over the open half-space are interior; that part is the image of a convex set, and $V\cap M^\circ_n$ lies in its closure, since the open half-space is dense in the half-space; so $V\cap M^\circ_n$ is connected or empty.
3. Suppose $M^\circ_n=A\sqcup B$ with $A,B$ open in $M^\circ_n$. Let $\hat A$ be the set of points of $M$ having a neighbourhood $V$ with $V\cap M^\circ_n\subseteq A$, and $\hat B$ likewise. Both are open, and they cover $M$ by step 2; $\hat A\supseteq A$ and $\hat B\supseteq B$.
4. They are disjoint: two such neighbourhoods of one point intersect in a neighbourhood of it, which meets $M^\circ_n$ by density, so the point cannot be in both.
5. $M$ is connected, so $\hat A$ or $\hat B$ is empty, and hence $A$ or $B$ is empty. With step 1, $M^\circ_n$ is connected.

## Sources

- [HS paper, Section 13](../../../sources/hs-paper.md#section-13-the-contradiction-seccontradiction-lines-1326-1391) (proof of Theorem 1.1, dimension 0 and boundary)
- New: an argument by half-balls, in place of local homology

## Depends on

- [Intrinsic interior](intrinsic-interior.md)

## Proof depends on

- [Points over the open half-space are interior](half-space-interior.md)
- [The open half-space is dense in the half-space](open-half-space-dense.md)
- [The intrinsic interior is dense](intrinsic-interior-dense.md)
