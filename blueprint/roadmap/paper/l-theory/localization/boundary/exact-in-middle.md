---
article_id: af_847856bdefdfec511a71ad12
declaration: lemma
origin: cited
---

# Exactness in the middle

Let $\mathcal U\subset\mathcal A$ be an involution-invariant Karoubi filtration. If $y\in L^p_k(\mathcal A)$ has $q^{\mathrm{im}}_*y=0$ in $L^{\mathrm{im}}_k(\mathcal A/\mathcal U)$, then $y=i_*z$ for some $z\in L^p_k(\mathcal U)$, where $i_*$ is the [induced homomorphism](../../base/groups/induced-map.md) of the inclusion.

*Proof sketch.* (1) Write $y=[C,\phi]$, and let $Z'$ be a complex of zero objects in $\mathrm{Kar}\,\mathcal U$ with zero structure. By [Closed complexes are pairs with zero boundary](closed-pair.md), $V=(0:iZ'\to C,\phi,0)$ is a strict $k$-dimensional [$\mathcal U$-pair](u-pair.md) over $(Z',0)$. Its image $qV=(qC,q_\%\phi)$ has class $q^{\mathrm{im}}_*y=0$ ([Quotient map into the decorated group](../decorations/quotient-map.md)). (2) By [Zero classes bound](../../base/groups/l-group-zero-iff-bounds.md) in $\mathrm{Dec}(\mathcal A/\mathcal U)$, $qV$ is the boundary of a strict $(k+1)$-dimensional pair $W$ in $\mathrm{Dec}(\mathcal A/\mathcal U)$. (3) Parts (a) and (b) of [Lifting](lift-to-pair.md) give $R=(Z'\to R_\bullet,\rho,0)$ in $\mathrm{Kar}\,\mathcal U$ and a strict pair in $\mathrm{Kar}\,\mathcal A$ with boundary the [closed union](closed-union.md) $(C\cup_{Z'}R,\Phi)$. By [Closed complexes are pairs with zero boundary](closed-pair.md), $(R_\bullet,\rho)$ is a strict $k$-dimensional Poincaré complex in $\mathrm{Kar}\,\mathcal U$, and by [Zero classes bound](../../base/groups/l-group-zero-iff-bounds.md), $[C\cup_{Z'}R,\Phi]=0$. (4) The chain objects of $C\cup_{Z'}R$ are $C_r\oplus iR_{\bullet,r}\oplus iZ'_{r-1}$. The last summand is a zero object and every cross term of $\Phi$ passes through it, so the inclusion of $C\oplus iR_\bullet$ is an isomorphism carrying $\phi\oplus i_\%\rho$ to $\Phi$. [Homotopy-isometry invariance](../../base/groups/homotopy-isometry-invariance.md) with $\chi=0$ and [Group structure on L](../../base/groups/l-group-add.md) give $[C,\phi]+i_*[R_\bullet,\rho]=0$. Take $z=-[R_\bullet,\rho]$.

## Sources

- New: group-level arrangement of [Carlsson-Pedersen 1995, Theorem 4.1](../../../../../sources/paper/carlsson-pedersen-1995.md) [U]

## Depends on

- [Quotient map into the decorated group](../decorations/quotient-map.md)
- [Induced homomorphism](../../base/groups/induced-map.md)

## Proof depends on

- [U-pairs](u-pair.md)
- [Closed complexes are pairs with zero boundary](closed-pair.md)
- [Zero classes bound](../../base/groups/l-group-zero-iff-bounds.md)
- [Lifting](lift-to-pair.md)
- [Closing a pair by a null-cobordism of its boundary](closed-union.md)
- [Homotopy-isometry invariance](../../base/groups/homotopy-isometry-invariance.md)
- [Group structure on L](../../base/groups/l-group-add.md)
