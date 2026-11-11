---
article_id: af_2168191d71ec9306bc24f5db
declaration: def
origin: background
statement: formalized
lean: HSP.strProd
---

# External product of structures

Let $(\boxtimes,\kappa):\mathcal B\times\mathcal E\to\mathcal B''$ be a [duality pairing](duality-pairing.md), $C$ a complex in $\mathcal B$ and $E$ a complex in $\mathcal E$, each with all but finitely many chain objects zero objects, and let $C\otimes E$ be their [tensor product](complex-product.md). For $\phi\in M(C)_m$ and $\theta\in M(E)_n$, the structure $\phi\otimes\theta\in M(C\otimes E)_{m+n}$ has, from the summand $C^*_{m-p}\boxtimes E^*_{n-q}$ of $(C\otimes E)^*_{m+n-p-q}$ (identified through $\kappa$) to $C_p\boxtimes E_q$, the block
$$(-1)^{q(p+m)}\,\phi_p\boxtimes\theta_q,$$
and zero blocks elsewhere. The degree $k=m+n$ of $\phi\otimes\theta$ is recorded as a number $k$ with $m+n=k$, so that structures of degrees $(m-1)+n$ and $m+n-1$ can be compared directly.

## Sources

- [Ranicki 1980 I, §8, products](../../../../../sources/paper/ranicki-1980.md) [U]
- New: the sign $(-1)^{q(p+m)}$ is the one for which the [Leibniz rule](product-leibniz.md), [compatibility with T](product-involution.md) and [the duality map of a product](product-duality-map.md) hold in the conventions of [Structure complex](../../base/complexes/structure-complex.md) and [Dual complex](../../base/complexes/dual-complex.md).

## Depends on

- [Duality pairings](duality-pairing.md)
- [Tensor product of complexes](complex-product.md)
- [Structure complex](../../base/complexes/structure-complex.md)
