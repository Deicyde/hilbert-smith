---
article_id: af_039979db2929e2316b04f8b6
declaration: abbrev
origin: background
statement: formalized
lean: HSP.cxProdMap
---

# Tensor product of chain maps

Let $(\boxtimes,\kappa):\mathcal B\times\mathcal E\to\mathcal B''$ be a [duality pairing](../duality-pairing.md), and let $f:C\to C'$ and $g:E\to E'$ be chain maps of complexes in $\mathcal B$ and $\mathcal E$, each with all but finitely many chain objects zero objects. The chain map $f\otimes g:C\otimes E\to C'\otimes E'$ of [tensor products](../complex-product.md) is $f_p\boxtimes g_q$ on the summand $C_p\boxtimes E_q$.

*Proof sketch.* (Proof obligations.) $f\otimes g$ commutes with the differentials because $f$ and $g$ do and the sign $(-1)^p$ depends only on $p$.

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
