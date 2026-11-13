---
article_id: af_27ccd0b4797a657ae51bbe22
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.isClosed_interior_fixSet
---

# Interiors of fixed sets are closed

Let $p$ be a prime and let $\mathbb Z_p$ act jointly continuously on an $n$-manifold $M$ (a Hausdorff space with an atlas of charts onto open subsets of $\mathbb R^n$, with no countability assumption). Suppose every point of $M$ has a neighbourhood fixed pointwise by some $H_m$. Then for every $j$ the interior $F_j$ of $\operatorname{Fix}_j(M)$ is closed.

*Proof sketch.* Take $x\in\overline{F_j}$.
1. $\operatorname{Fix}_j(M)$ is closed, so $H_j$ fixes $x$.
2. By hypothesis $x$ lies in the open set $N=\operatorname{int}\operatorname{Fix}_m(M)$ for some $m$.
3. $H_jx=\{x\}\subseteq N$, so compactness of $H_j$ and the tube lemma give an open $V\ni x$ with $H_jV\subseteq N$; since $M$ is locally connected, the connected component $B$ of $V$ containing $x$ is a connected open neighbourhood of $x$ with $H_jB\subseteq N$.
4. The saturation $N'=H_jB$ is open, $H_j$-invariant, and connected, since every translate of $B$ contains $x$. As an open subset of $M$ it is a connected $n$-manifold.
5. Each $a\in H_j$ restricts to a homeomorphism of $N'$ whose $p^m$-th power is the identity, because $p^m a\in H_m$ fixes $N\supseteq N'$. It fixes pointwise the open set $N'\cap F_j$, which is nonempty because $x\in\overline{F_j}$.
6. Newman's theorem on fixing an open set makes $a$ the identity on $N'$. So $N'\subseteq\operatorname{Fix}_j(M)$, and $x\in F_j$.

This lemma rests on the open statement [Newman's theorem on fixing an open set](../../inputs/newman/newman-open-set.md).

## Sources

- [OpenAI preprint, Section 5](../../../../sources/preprint.md#section-5-local-tests-sections05-local-teststex), 05-local-tests.tex lines 36-50

## Depends on

- [Fixed sets of the subgroups $H_j$](fixed-sets.md)

## Proof depends on

- [Fixed sets are closed](fixed-sets-closed.md)
- [The subgroups $H_j$ form a basis at $0$](padic-subgroups-basis.md)
- [Newman's theorem: fixing an open set](../../inputs/newman/newman-open-set.md)
- [The subgroups $H_j$](padic-subgroups.md)
