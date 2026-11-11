---
article_id: af_e998e651ca01fdcf9019c5ac
declaration: def
origin: cited
statement: formalized
lean: HSP.transitionCx
---

# Product of a complex with the line

For $j\ge0$ and a strict $m$-dimensional symmetric Poincaré complex $(C,\phi)$ in $\operatorname{Kar}C_{\mathbb Z^j}\mathcal A$, the product $(C\otimes\Lambda,\phi\otimes\lambda)$ for the [box product pairing](../products/box-dual.md) is a strict $(m+1)$-dimensional symmetric Poincaré complex in $\operatorname{Kar}C_{\mathbb Z^{j+1}}\mathcal A$.

*Proof sketch.* Its chain objects are zero objects outside $[0,m+1]$; $T(\phi\otimes\lambda)=\phi\otimes\lambda$ and $\partial(\phi\otimes\lambda)=0$ by [Products commute with T](../products/product-involution.md), the [Leibniz rule](../products/product-leibniz.md) and [The symmetric line is a symmetric complex](../products/symmetric-line-cycle.md); and $(\phi\otimes\lambda)_\natural=(\phi_\natural\otimes\lambda_\natural)\circ\Xi$ ([Duality map of a product](../products/product-duality-map.md)) is an equivalence by [Tensor products of equivalences](../products/product-equivalence.md) and [The line is Poincaré](../products/symmetric-line-poincare.md).

## Sources

- [Ranicki 1992, §17](../../../../../sources/paper/ranicki-1992.md) [U]
- New: step 1 of the transition map, split out.

## Depends on

- [Box product on iterated bounded categories](../products/box-pairing-pow.md)
- [Strict symmetric Poincaré complex](../../base/pairs/symmetric-poincare-complex.md)
- [Tensor product of complexes](../products/complex-product.md)
- [External product of structures](../products/external-product.md)
- [The symmetric line](../products/symmetric-line.md)
- [Structure of the symmetric line](../products/symmetric-line-structure.md)
- [Duals of box products](../products/box-dual.md)

## Proof depends on

- [Products commute with T](../products/product-involution.md)
- [Leibniz rule for products](../products/product-leibniz.md)
- [The symmetric line is a symmetric complex](../products/symmetric-line-cycle.md)
- [Duality map of a product](../products/product-duality-map.md)
- [Dual of a tensor product](../products/product-dual-iso.md)
- [Tensor products of equivalences](../products/product-equivalence.md)
- [The line is Poincaré](../products/symmetric-line-poincare.md)
