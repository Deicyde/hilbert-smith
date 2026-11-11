---
article_id: af_bec907cda187aafbd826b950
declaration: lemma
origin: cited
---

# Lifting closed complexes

Let $\mathcal U\subset\mathcal A$ be an involution-invariant Karoubi filtration. For every $x\in L^{\mathrm{im}}_k(\mathcal A/\mathcal U)$ there is a strict $k$-dimensional [$\mathcal U$-pair](u-pair.md) $V$ with $[qV]=x$.

This lemma rests on the open statement [Lifting](lift-to-pair.md).

*Proof sketch.* (1) Write $x=[C,\phi]$ with $C$ in $\mathrm{Dec}(\mathcal A/\mathcal U)$. Let $V_0$ be the zero $(k-1)$-dimensional $\mathcal U$-pair: $P_0$ and $D_0$ are complexes of zero objects with zero structures, a pair by [Closed complexes are pairs with zero boundary](closed-pair.md). Its image $qV_0$ is a complex of zero objects, so by the same lemma $W=(0:qD_0\to C,\phi,0)$ is a strict $k$-dimensional pair in $\mathrm{Dec}(\mathcal A/\mathcal U)$ with boundary $qV_0$. (2) [Lifting](lift-to-pair.md) for $V_0$ and $W$ gives $R=(P_0\to R_\bullet,\rho,0)$ and $E=(e:D_0\cup_{P_0}R\to E_\bullet,\delta\epsilon,\Phi)$. By [Closed complexes are pairs with zero boundary](closed-pair.md), $(R_\bullet,\rho)$ is a strict $(k-1)$-dimensional Poincaré complex in $\mathrm{Kar}\,\mathcal U$. (3) In $D_0\cup_{P_0}R$ every summand except $iR_{\bullet,r}$ is a zero object, and every cross term of $\Phi$ passes through one. So the inclusion $j:iR_\bullet\to D_0\cup_{P_0}R$ is an isomorphism of complexes carrying $i_\%\rho$ to $\Phi$. By [Pair transport](../../base/pairs/pair-transport.md), $V=(e\circ j:iR_\bullet\to E_\bullet,\delta\epsilon,i_\%\rho)$ is a strict $k$-dimensional $\mathcal U$-pair, with image $qV=(qE_\bullet,q_\%\delta\epsilon)$. (4) For the same reason the inclusion of $C\oplus qE_\bullet$ into $W\cup(-E^\sharp)$ is an isomorphism carrying $\phi\oplus(-q_\%\delta\epsilon)$ to its structure. Part (c) of Lifting, [Homotopy-isometry invariance](../../base/groups/homotopy-isometry-invariance.md) with $\chi=0$, [Group structure on L](../../base/groups/l-group-add.md) and [Negation in L](../../base/groups/l-group-neg.md), all in $\mathrm{Dec}(\mathcal A/\mathcal U)$, give $0=[C,\phi]-[qV]$.

## Sources

- [Carlsson-Pedersen 1995, Section 4](../../../../../sources/paper/carlsson-pedersen-1995.md) [U]
- New: derived from the relative form of [Lifting](lift-to-pair.md)

## Depends on

- [U-pairs](u-pair.md)
- [Image of a pair with boundary in Kar U](image-pair.md)
- [Decorated quotient L-group](../decorations/decorated-l-group.md)

## Proof depends on

- [Lifting](lift-to-pair.md)
- [Closed complexes are pairs with zero boundary](closed-pair.md)
- [Pair transport](../../base/pairs/pair-transport.md)
- [Homotopy-isometry invariance](../../base/groups/homotopy-isometry-invariance.md)
- [Group structure on L](../../base/groups/l-group-add.md)
- [Negation in L](../../base/groups/l-group-neg.md)
