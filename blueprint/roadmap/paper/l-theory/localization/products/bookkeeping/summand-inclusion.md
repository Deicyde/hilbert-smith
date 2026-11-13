---
article_id: af_056a6df53dd03abb7cde1288
declaration: abbrev
origin: background
statement: formalized
lean: HSP.cxProd.ι
---

# Summand inclusions of a tensor product

Let $(\boxtimes,\kappa):\mathcal B\times\mathcal E\to\mathcal B''$ be a [duality pairing](../duality-pairing.md), and $C$ a complex in $\mathcal B$ and $E$ a complex in $\mathcal E$, each with all but finitely many chain objects zero objects. For $p,q,r\in\mathbb Z$ the map $\iota_{p,q}:C_p\boxtimes E_q\to(C\otimes E)_r$ into the [tensor product](../complex-product.md) $C\otimes E$ is the inclusion of the summand $C_p\boxtimes E_q$ when $p+q=r$, and $0$ otherwise.

## Sources

- [Ranicki 1980 I, §8, products](../../../../../../sources/paper/ranicki-1980.md) [U]

## Depends on

- [Duality pairings](../duality-pairing.md)
- [Tensor product of complexes](../complex-product.md)
- [Small Q-linear category with strict duality](../../../base/categories/duality-category.md)

## Proof depends on

- [A duality pairing is additive in the first variable](pairing-additive-left.md)
- [A duality pairing is additive in the second variable](pairing-additive-right.md)
- [The sums in a tensor product of complexes exist](product-sums-exist.md)
- [Signs for tensor products of chain complexes](tensor-signs.md)
