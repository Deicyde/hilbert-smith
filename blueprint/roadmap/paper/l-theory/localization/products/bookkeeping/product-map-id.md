---
article_id: af_e5f78fe866dfb03876e4185b
declaration: lemma
origin: background
statement: formalized
lean: HSP.cxProdMap_id
proof: formalized
---

# Tensor product of identities

Let $(\boxtimes,\kappa):\mathcal B\times\mathcal E\to\mathcal B''$ be a [duality pairing](../duality-pairing.md), and $C$ a complex in $\mathcal B$ and $E$ a complex in $\mathcal E$, each with all but finitely many chain objects zero objects. Then $1_C\otimes1_E=1_{C\otimes E}$ as [tensor products of chain maps](product-map.md).

*Proof sketch.* On each summand $C_p\boxtimes E_q$ the left side is $1_{C_p}\boxtimes1_{E_q}=1$.

## Sources

- New: functoriality, direct from the definition.

## Depends on

- [Duality pairings](../duality-pairing.md)
- [Tensor product of chain maps](product-map.md)
- [Small Q-linear category with strict duality](../../../base/categories/duality-category.md)
- [Tensor product of complexes](../complex-product.md)

## Proof depends on

- [A duality pairing is additive in the first variable](pairing-additive-left.md)
- [A duality pairing is additive in the second variable](pairing-additive-right.md)
- [The sums in a tensor product of complexes exist](product-sums-exist.md)
- [Signs for tensor products of chain complexes](tensor-signs.md)
