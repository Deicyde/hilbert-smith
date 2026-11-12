---
article_id: af_66215d157fd5163eb4303c88
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: HSP.oneChart
---

# Reduction to one chart

Let $p$ be a prime and let $\mathbb{Z}_p$ act jointly continuously and faithfully on a connected $n$-manifold $M$, with no countability assumed. Then there are a nonempty connected open set $O\subseteq\mathbb{R}^n$ and a jointly continuous faithful action of $\mathbb{Z}_p$ on $O$.

*Proof sketch.*
1. Take a point $x$ with no fixed neighbourhood, and a chart $e$ at $x$ with a coordinate ball $B\ni x$ whose closure is compact in the domain of $e$.
2. Uniformly small displacement near the identity and the basis property of the $H_j$ give $j$ with $H_j\overline B$ inside the domain of $e$ and $H_jx\subseteq B$.
3. $O'=H_jB$ is open, $H_j$-invariant, and connected, since each translate $aB$ meets $B$ at $a\cdot x$.
4. The subgroup of elements of $\mathbb{Z}_p$ fixing $O'$ pointwise is a closed subgroup of $\mathbb{Z}_p$, an intersection of stabilizers in the Hausdorff space $M$. A nonzero such subgroup would be some $H_i$ by the classification of closed subgroups, and it would fix the neighbourhood $O'$ of $x$ pointwise, which the choice of $x$ excludes. So it is zero.
5. Let $\mathbb{Z}_p$ act on $O=e(O')$ by $a\star y=e((p^ja)\cdot e^{-1}(y))$. This action is jointly continuous, and faithful by step 4.

The open set $O$ is second countable as a subset of $\mathbb{R}^n$, so no second countability of $M$ is needed.

This result rests, through the good point, on the open statement [Newman's theorem on fixing an open set](../inputs/newman/newman-open-set.md).

## Sources

- [OpenAI preprint, Section 5](../../../sources/preprint.md#section-5-local-tests-sections05-local-teststex), 05-local-tests.tex lines 51-66
- [HS paper, Section 8](../../../sources/hs-paper.md#section-8-geometric-data-and-quotient-representatives-geofixed-data-lines-755-846) (a chart and a small subgroup, reached differently)

## Depends on

## Proof depends on

- [A point with no fixed neighbourhood](../local-data/subgroups/good-point.md)
- [Uniformly small displacement near the identity](../local-data/subgroups/small-displacement.md)
- [The subgroups $H_j$ form a basis at $0$](../local-data/subgroups/padic-subgroups-basis.md)
- [Closed subgroups of $\mathbb Z_p$](../local-data/subgroups/closed-subgroups.md)
- [The subgroups $H_j$](../local-data/subgroups/padic-subgroups.md)
