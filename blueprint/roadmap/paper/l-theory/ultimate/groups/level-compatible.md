---
article_id: af_e95e508d3d22e22ae0953ba1
declaration: lemma
origin: background
statement: formalized
lean: HSP.ultL.of_trans
proof: formalized
---

# Stages are compatible with the transition

$\iota_{j+1}\circ t=\iota_j$ on $L^{\langle -j\rangle}_k(\mathcal A)$, for the [stage maps](ultimate-stage-map.md) $\iota_j$. Hence $\iota_{j+m}\circ t^m=\iota_j$ for every $m\ge0$. Here $t^m:L^{\langle -j\rangle}_k(\mathcal A)\to L^{\langle -j-m\rangle}_k(\mathcal A)$ is the [iterated transition](transition-iter.md).

*Proof sketch.* The first identity is the compatibility of the maps into a colimit with the transition maps of the [sequence of lower L-groups](lower-l-sequence.md). The second follows by induction on $m$, since $t^{m+1}=t\circ t^m$.

## Sources

- New: property of the colimit.

## Depends on

- [Stage maps into the ultimate L-group](ultimate-stage-map.md)
- [Iterated transition](transition-iter.md)
- [Lower transition map](../../localization/transitions/transition-lower.md)
- [Small Q-linear category with strict duality](../../base/categories/duality-category.md)
- [Idempotent completion with duality](../../base/categories/karoubi-duality.md)
- [Group structure on L](../../base/groups/l-group-add.md)
- [Iterated bounded categories](../../bounded/categories/iterated-bounded-category.md)
- [Lower L-group](../../localization/transitions/lower-l-group.md)
- [Ultimate L-group](ultimate-l-group.md)

## Proof depends on

- [Sequence of lower L-groups](lower-l-sequence.md)
