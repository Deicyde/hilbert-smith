---
article_id: af_5f4486e992af67598310f3c5
declaration: def
origin: cited
statement: formalized
lean: HSP.locBoundary
---

# Localization boundary

Let $\mathcal U\subset\mathcal A$ be an involution-invariant Karoubi filtration. For $x\in L^{\mathrm{im}}_k(\mathcal A/\mathcal U)$ choose, by [Lifting closed complexes](lift-to-pair-closed.md), a strict $k$-dimensional [$\mathcal U$-pair](u-pair.md) $V_x$ over $(P_x,\pi_x)$ with $[qV_x]=x$. The *localization boundary* is the homomorphism
$$\partial:L^{\mathrm{im}}_k(\mathcal A/\mathcal U)\to L^p_{k-1}(\mathcal U),\qquad x\mapsto[P_x,\pi_x].$$

This definition rests on the open statement [Lifting](lift-to-pair.md), through [Lifting closed complexes](lift-to-pair-closed.md).

*Proof sketch.* (Additivity.) By [Sums of U-pairs](u-pair-sum.md) there is a $\mathcal U$-pair $V$ with $[qV]=x+y$ and boundary class $[P_x,\pi_x]+[P_y,\pi_y]$. [Independence of the lift](boundary-independence.md), applied to $V$ and $V_{x+y}$, gives $\partial(x+y)=\partial x+\partial y$.

## Sources

- New: group-level arrangement of [Carlsson-Pedersen 1995, Theorem 4.1](../../../../../sources/paper/carlsson-pedersen-1995.md) [U]
- HS paper, Section 6

## Depends on

- [Involution-invariant Karoubi filtration](../../base/categories/karoubi-filtration.md)
- [U-pairs](u-pair.md)
- [Decorated quotient L-group](../decorations/decorated-l-group.md)
- [Image of a pair with boundary in Kar U](image-pair.md)
- [Lifting closed complexes](lift-to-pair-closed.md)
- [L-group](../../base/groups/l-group.md)
- [The projective L-group](../../base/groups/projective-l-group.md)

## Proof depends on

- [Sums of U-pairs](u-pair-sum.md)
- [Independence of the lift](boundary-independence.md)
