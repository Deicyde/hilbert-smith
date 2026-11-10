---
article_id: af_415eb06a487df90375eefff7
declaration: lemma
origin: cited
---

# Exactness at the quotient

Let $\mathcal U\subset\mathcal A$ be an involution-invariant Karoubi filtration. If $x\in L^{\mathrm{im}}_k(\mathcal A/\mathcal U)$ has $\partial x=0$, then $x=q^{\mathrm{im}}_*y$ for some $y\in L^p_k(\mathcal A)$, where $q^{\mathrm{im}}_*$ is the [quotient map into the decorated group](../decorations/quotient-map.md).

*Proof sketch.* (1) By [Lifting closed complexes](lift-to-pair-closed.md), $x=[qV]$ for a [$\mathcal U$-pair](u-pair.md) $V=(f:iP\to D,\delta\phi,i_\%\pi)$. (2) By the [pair formula](pair-formula.md), $[P,\pi]=\partial x=0$, so $[P,-\pi]=0$ by [Negation in L^p](../../base/groups/l-group-neg.md). By [Zero classes bound](../../base/groups/l-group-zero-iff-bounds.md), $(P,-\pi)$ is the boundary of a strict $k$-dimensional pair $R$ in $\mathrm{Kar}\,\mathcal U$. (3) The [closed union](closed-union.md) $(D\cup_PR,\Phi)$ is a strict $k$-dimensional Poincaré complex in $\mathrm{Kar}\,\mathcal A$; put $y=[D\cup_PR,\Phi]$. (4) By the definition of $q^{\mathrm{im}}_*$, $q^{\mathrm{im}}_*y=[q(D\cup_PR),q_\%\Phi]$. The isomorphism $p$ of [The closed union becomes the image of the pair](union-image.md) carries $q_\%\Phi$ to $q_\%\delta\phi$, so [Homotopy-isometry invariance](../../base/groups/homotopy-isometry-invariance.md) in $\mathrm{Dec}(\mathcal A/\mathcal U)$, with $h=p$ and $\chi=0$, gives $q^{\mathrm{im}}_*y=[qV]=x$.

## Sources

- New: group-level arrangement of [Carlsson-Pedersen 1995, Theorem 4.1](../../../../../sources/paper/carlsson-pedersen-1995.md) [U]

## Depends on

- [Localization boundary](localization-boundary.md)
- [Quotient map into the decorated group](../decorations/quotient-map.md)

## Proof depends on

- [U-pairs](u-pair.md)
- [Lifting closed complexes](lift-to-pair-closed.md)
- [Pair formula](pair-formula.md)
- [Negation in L^p](../../base/groups/l-group-neg.md)
- [Zero classes bound](../../base/groups/l-group-zero-iff-bounds.md)
- [Closing a pair by a null-cobordism of its boundary](closed-union.md)
- [The closed union becomes the image of the pair](union-image.md)
- [Homotopy-isometry invariance](../../base/groups/homotopy-isometry-invariance.md)
