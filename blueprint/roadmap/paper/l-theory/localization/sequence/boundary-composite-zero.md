---
article_id: af_684ced9c1ae308426fcdd943
declaration: lemma
origin: background
---

# Boundary then inclusion is zero

Let $\mathcal U\subset\mathcal A$ be an involution-invariant Karoubi filtration, and let $i_*:L^p_{k-1}(\mathcal U)\to L^p_{k-1}(\mathcal A)$ be the [induced homomorphism](../../base/groups/induced-map.md) of the inclusion. Then $i_*\circ\partial=0$ on $L^{\mathrm{im}}_k(\mathcal A/\mathcal U)$.

*Proof sketch.* Let $x\in L^{\mathrm{im}}_k(\mathcal A/\mathcal U)$. By [Lifting closed complexes](lift-to-pair-closed.md), $x=[qV]$ for a $\mathcal U$-pair $V=(f:iP\to D,\delta\phi,i_\%\pi)$. By the [pair formula](pair-formula.md), $i_*\partial x=i_*[P,\pi]=[iP,i_\%\pi]$. This complex is the boundary of $V$, so its class is $0$ by [Zero classes bound](../../base/groups/l-group-zero-iff-bounds.md).

## Sources

- New: group-level arrangement of [Carlsson-Pedersen 1995, Theorem 4.1](../../../../../sources/paper/carlsson-pedersen-1995.md) [U]; the lift is a null-cobordism in $\mathrm{Kar}\,\mathcal A$

## Depends on

- [Localization boundary](localization-boundary.md)
- [Induced homomorphism](../../base/groups/induced-map.md)

## Proof depends on

- [Lifting closed complexes](lift-to-pair-closed.md)
- [Pair formula](pair-formula.md)
- [Zero classes bound](../../base/groups/l-group-zero-iff-bounds.md)
