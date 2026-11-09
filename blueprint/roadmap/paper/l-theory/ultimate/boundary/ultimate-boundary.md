---
article_id: af_723f83ce92dedcbb8d75baf1
declaration: def
origin: cited
---

# Ultimate boundary

Let $\mathcal U\subset\mathcal A$ be an involution-invariant Karoubi filtration. $\partial:\mathbb L_k(\mathcal A/\mathcal U)\to\mathbb L_{k-1}(\mathcal U)$ is the homomorphism out of the colimit given at level $j$ by
$$x\longmapsto\sigma_{k,j}\,\iota_{j+1}\big(\partial^{(j)}x\big),\qquad x\in L^{\langle -j\rangle}_k(\mathcal A/\mathcal U),$$
where $\partial^{(j)}:L^{\langle -j\rangle}_k(\mathcal A/\mathcal U)\to L^{\langle -j-1\rangle}_{k-1}(\mathcal U)$ is the [level boundary](../../localization/line/level-boundary.md) and $\sigma_{k,j}$ the [boundary sign](boundary-sign.md). These maps are compatible with $t$: by [Levels are compatible with the transition](../groups/level-compatible.md) and [Transition commutes with the boundary](../../localization/line/transition-boundary-commute.md), which states $t\circ\partial^{(j)}=\eta_{k+j+1}\,\partial^{(j+1)}\circ t$,
$$\sigma_{k,j}\,\iota_{j+1}\partial^{(j)}x=\sigma_{k,j}\,\iota_{j+2}\,t\,\partial^{(j)}x=\sigma_{k,j}\eta_{k+j+1}\,\iota_{j+2}\,\partial^{(j+1)}tx=\sigma_{k,j+1}\,\iota_{j+2}\,\partial^{(j+1)}tx.$$

## Sources

- [Carlsson-Pedersen 1995, Thm 4.2, spectrum-level boundary](../../../../../sources/paper/carlsson-pedersen-1995.md) [U]
- New: the group-level colimit of the level boundaries, with the sign $\sigma_{k,j}$.

## Depends on

- [Ultimate L-group](../groups/ultimate-l-group.md)
- [Level boundary](../../localization/line/level-boundary.md)
- [Boundary sign](boundary-sign.md)
- [Transition commutes with the boundary](../../localization/line/transition-boundary-commute.md)
- [Levels are compatible with the transition](../groups/level-compatible.md)
