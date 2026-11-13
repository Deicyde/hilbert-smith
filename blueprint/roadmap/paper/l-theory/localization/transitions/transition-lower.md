---
article_id: af_4c91755ef8017159623e55af
declaration: abbrev
origin: cited
statement: formalized
lean: HSP.transitionLower
---

# Lower transition map

For $j\ge0$ and $k\in\mathbb Z$, the [transition map](transition-map.md) at $m=k+j$ is a homomorphism
$$t:L^{\langle -j\rangle}_k(\mathcal A)\to L^{\langle -j-1\rangle}_k(\mathcal A),$$
since $L^{\langle -j\rangle}_k(\mathcal A)=L^p_{k+j}(C_{\mathbb Z^j}\mathcal A)$ ([Lower L-group](lower-l-group.md)) and $k+j+1=k+(j+1)$.

## Sources

- [Ranicki 1992, §17](../../../../../sources/paper/ranicki-1992.md) [U]
- New: the stage bookkeeping, split out of the transition map.

## Depends on

- [Small Q-linear category with strict duality](../../base/categories/duality-category.md)
- [Lower L-group](lower-l-group.md)
- [Idempotent completion with duality](../../base/categories/karoubi-duality.md)
- [Group structure on L](../../base/groups/l-group-add.md)
- [Iterated bounded categories](../../bounded/categories/iterated-bounded-category.md)

## Proof depends on

- [Transition map](transition-map.md)
