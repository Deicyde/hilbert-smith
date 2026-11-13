---
article_id: af_762f1816b10789da900cad8a
declaration: def
origin: background
statement: formalized
lean: HSP.lowerLSeq
---

# Sequence of lower L-groups

For a duality category $\mathcal A$ and $k\in\mathbb Z$, the *sequence of lower L-groups* is the diagram of abelian groups over $(\mathbb N,\le)$
$$L^{\langle 0\rangle}_k(\mathcal A)\xrightarrow{t}L^{\langle -1\rangle}_k(\mathcal A)\xrightarrow{t}L^{\langle -2\rangle}_k(\mathcal A)\xrightarrow{t}\cdots$$
of the [lower L-groups](../../localization/transitions/lower-l-group.md) and the [transition maps](../../localization/transitions/transition-lower.md) $t$. The map from stage $j$ to stage $j'\ge j$ is the composite of the transitions between them.

## Sources

- [Ranicki 1992, §17](../../../../../sources/paper/ranicki-1992.md) [U]

## Depends on

- [Small Q-linear category with strict duality](../../base/categories/duality-category.md)

## Proof depends on

- [Idempotent completion with duality](../../base/categories/karoubi-duality.md)
- [Group structure on L](../../base/groups/l-group-add.md)
- [Iterated bounded categories](../../bounded/categories/iterated-bounded-category.md)
- [Lower L-group](../../localization/transitions/lower-l-group.md)
- [Lower transition map](../../localization/transitions/transition-lower.md)
