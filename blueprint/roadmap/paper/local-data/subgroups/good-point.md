---
article_id: af_76e0960710c35845a2099231
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: HSP.exists_good_point
---

# A point with no fixed neighbourhood

Let $p$ be a prime and let $\mathbb Z_p$ act jointly continuously and faithfully on a connected $n$-manifold $M$ (a connected Hausdorff space with an atlas of charts onto open subsets of $\mathbb R^n$, with no countability assumption). Then there is $x\in M$ such that, for every $j$, $\operatorname{Fix}_j(M)$ is not a neighbourhood of $x$.

*Proof sketch.* Suppose every point has a neighbourhood fixed pointwise by some $H_j$.
1. Each $F_j=\operatorname{int}\operatorname{Fix}_j(M)$ is open, and closed by the lemma on interiors of fixed sets.
2. $M$ is nonempty, being connected. At a point of $M$ some $\operatorname{Fix}_j(M)$ is a neighbourhood, so that $F_j$ is nonempty.
3. Being clopen in the connected $M$, that $F_j$ equals $M$. Then $p^j\ne0$ acts trivially, which contradicts faithfulness.

This result rests, through the lemma on interiors of fixed sets, on the open statement [Newman's theorem on fixing an open set](../../inputs/newman/newman-open-set.md).

## Sources

- [OpenAI preprint, Section 5](../../../../sources/preprint.md#section-5-local-tests-sections05-local-teststex), 05-local-tests.tex lines 30-50
- [HS paper, Section 8](../../../../sources/hs-paper.md#section-8-geometric-data-and-quotient-representatives-geofixed-data-lines-755-846) (a different point, with trivial stabilizer; not used here)

## Depends on

- [Fixed sets of the subgroups $H_j$](fixed-sets.md)

## Proof depends on

- [Interiors of fixed sets are closed](interior-fixed-set-closed.md)
