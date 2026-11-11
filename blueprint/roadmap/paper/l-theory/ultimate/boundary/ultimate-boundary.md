---
article_id: af_723f83ce92dedcbb8d75baf1
declaration: def
origin: cited
statement: formalized
lean: HSP.ultBoundary
---

# Ultimate boundary

Let $\mathcal U\subset\mathcal A$ be an involution-invariant Karoubi filtration. $\partial:\mathbb L_k(\mathcal A/\mathcal U)\to\mathbb L_{k-1}(\mathcal U)$ is the homomorphism out of the colimit given at stage $j$ by
$$x\longmapsto\iota_{j+1}\big(\partial^{(j)}x\big),\qquad x\in L^{\langle -j\rangle}_k(\mathcal A/\mathcal U),$$
where $\partial^{(j)}:L^{\langle -j\rangle}_k(\mathcal A/\mathcal U)\to L^{\langle -j-1\rangle}_{k-1}(\mathcal U)$ is the [stage boundary](../../localization/transitions/level-boundary.md). These maps are compatible with $t$: by [Stages are compatible with the transition](../groups/level-compatible.md) and [Transition commutes with the boundary](../../localization/transitions/transition-boundary-commute.md),
$$\iota_{j+1}\partial^{(j)}x=\iota_{j+2}\,t\,\partial^{(j)}x=\iota_{j+2}\,\partial^{(j+1)}tx.$$

This definition rests on the open statement [Lifting](../../localization/boundary/lift-to-pair.md), through the stage boundaries.

Here $\partial^{(j)}x$ is read in $L^{\langle -j-1\rangle}_{k-1}(\mathcal U)$ through [Iterated bounded categories of a subcategory](sub-pow-identification.md), as in [Transition commutes with the boundary](../../localization/transitions/transition-boundary-commute.md), and the colimit maps are the [stage maps](../groups/ultimate-stage-map.md) of the [sequence of lower L-groups](../groups/lower-l-sequence.md).

## Sources

- [Carlsson-Pedersen 1995, Thm 4.2, spectrum-level boundary](../../../../../sources/paper/carlsson-pedersen-1995.md) [U]
- New: the group-level colimit of the stage boundaries.

## Depends on

- [Ultimate L-group](../groups/ultimate-l-group.md)
- [Stage boundary](../../localization/transitions/level-boundary.md)
- [Transition commutes with the boundary](../../localization/transitions/transition-boundary-commute.md)
- [Stages are compatible with the transition](../groups/level-compatible.md)
- [Iterated bounded categories of a subcategory](sub-pow-identification.md)
- [Stage maps into the ultimate L-group](../groups/ultimate-stage-map.md)
- [Sequence of lower L-groups](../groups/lower-l-sequence.md)
- [The class map](../groups/ultimate-cls.md)
