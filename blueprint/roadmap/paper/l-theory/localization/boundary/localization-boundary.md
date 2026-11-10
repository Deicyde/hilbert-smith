---
article_id: af_5f4486e992af67598310f3c5
declaration: def
origin: cited
---

# Localization boundary

Let $\mathcal U\subset\mathcal A$ be an involution-invariant Karoubi filtration. For $x\in L^{\mathrm{im}}_k(\mathcal A/\mathcal U)$ choose, by [Lifting closed complexes](lift-to-pair-closed.md), a strict $k$-dimensional [$\mathcal U$-pair](u-pair.md) $V_x$ over $(P_x,\pi_x)$ with $[qV_x]=x$. The *localization boundary* is the homomorphism
$$\partial:L^{\mathrm{im}}_k(\mathcal A/\mathcal U)\to L^p_{k-1}(\mathcal U),\qquad x\mapsto[P_x,\pi_x].$$

*Proof sketch.* (Additivity.) As in step (1) of [Independence of the lift](boundary-independence.md), but without negation: by [Sums of pairs](../../base/pairs/sum-of-pairs.md) and [Pair transport](../../base/pairs/pair-transport.md), $V_x\oplus V_y$ becomes a $\mathcal U$-pair over $(P_x\oplus P_y,\pi_x\oplus\pi_y)$. The canonical isomorphism $q(D_x\oplus D_y)\cong qD_x\oplus qD_y$ and [Homotopy-isometry invariance](../../base/groups/homotopy-isometry-invariance.md) in $\mathrm{Dec}(\mathcal A/\mathcal U)$ show that its image has class $x+y$. [Independence of the lift](boundary-independence.md) and [Group structure on L^p](../../base/groups/l-group-add.md) give $\partial(x+y)=[P_x\oplus P_y,\pi_x\oplus\pi_y]=\partial x+\partial y$.

## Sources

- New: group-level arrangement of [Carlsson-Pedersen 1995, Theorem 4.1](../../../../../sources/paper/carlsson-pedersen-1995.md) [U]
- HS paper, Section 6

## Depends on

- [U-pairs](u-pair.md)
- [Decorated quotient L-group](../decorations/decorated-l-group.md)
- [Image of a pair with boundary in Kar U](image-pair.md)
- [Lifting closed complexes](lift-to-pair-closed.md)
- [L-group](../../base/groups/l-group.md)

## Proof depends on

- [Sums of pairs](../../base/pairs/sum-of-pairs.md)
- [Pair transport](../../base/pairs/pair-transport.md)
- [Homotopy-isometry invariance](../../base/groups/homotopy-isometry-invariance.md)
- [Independence of the lift](boundary-independence.md)
- [Group structure on L^p](../../base/groups/l-group-add.md)
