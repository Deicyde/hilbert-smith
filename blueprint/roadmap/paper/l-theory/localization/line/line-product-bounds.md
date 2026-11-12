---
article_id: af_c6f9981a754f17d02cb3fdbc
declaration: lemma
origin: background
statement: formalized
lean: HSP.cxProd_line_isZero
proof: formalized
---

# Bounds of products with the line

Let $C$ be a complex in $\operatorname{Kar}C_{\mathbb Z^j}\mathcal A$ whose chain objects are zero objects outside degrees $[0,m]$. Then the chain objects of its [product](../products/complex-product.md) $C\otimes\Lambda$ with the [symmetric line](../products/symmetric-line.md), for the [box product pairing](../products/box-pairing-pow.md), are zero objects outside degrees $[0,m+1]$.

*Proof sketch.* $(C\otimes\Lambda)_r$ is the direct sum of the $C_p\boxtimes\Lambda_q$ with $p+q=r$, and only the summands with $0\le p\le m$ and $q\in\{0,1\}$ can be nonzero ([Support of a tensor product of complexes](../products/bookkeeping/product-support.md)).

## Sources

- New: degree bookkeeping.

## Depends on

- [Tensor product of complexes](../products/complex-product.md)
- [The symmetric line](../products/symmetric-line.md)
- [Box product on iterated bounded categories](../products/box-pairing-pow.md)

## Proof depends on

- [Support of a tensor product of complexes](../products/bookkeeping/product-support.md)
- [A tensor product is the sum of its summands](../products/bookkeeping/product-total.md)
