---
article_id: af_95b12b0869f2fcc24caf6fa1
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: HSP.exists_fixedLocalData
---

# Fixed local data from a faithful action

Let $p$ be a prime, let $\mathbb Z_p$ act jointly continuously and faithfully on a connected $n$-manifold $M$ (a connected Hausdorff space with an atlas of charts onto open subsets of $\mathbb R^n$, with no countability assumption), and let $0<D\le1/64$. Then for some $\rho_+\in(0,1/4)$ there are fixed local data in dimension $n$ with constants $(D,\rho_+)$.

*Proof sketch.* Take a local datum from the faithful action, then $\rho=\rho_+/2$ and $(r,R,t,u)=(1,2,3,4)$.

This result rests, through the local datum, on the open statement [Newman's theorem on fixing an open set](../../inputs/newman/newman-open-set.md).

## Sources

- [HS paper, Section 8](../../../../sources/hs-paper.md#section-8-geometric-data-and-quotient-representatives-geofixed-data-lines-755-846)

## Depends on

- [Fixed local data](fixed-local-data.md)

## Proof depends on

- [A local datum from a faithful action](../chart/local-datum-exists.md)
- [Local datum](../chart/local-datum.md)
