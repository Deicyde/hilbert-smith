---
article_id: af_4857639783789f947085c969
declaration: def
origin: cited
statement: formalized
lean: HSP.transitionMap
---

# Transition map

For $j\ge0$ and $m\in\mathbb Z$, the transition map
$$t:L^p_m(C_{\mathbb Z^j}\mathcal A)\to L^p_{m+1}(C_{\mathbb Z^{j+1}}\mathcal A),\qquad [C,\phi]\mapsto[C\otimes\Lambda,\phi\otimes\lambda],$$
is a well-defined homomorphism.

*Proof sketch.*
1. Complexes. $(C\otimes\Lambda,\phi\otimes\lambda)$ is a strict $(m+1)$-dimensional symmetric Poincaré complex ([Product of a complex with the line](transition-complex.md)).
2. Cobordisms. A [cobordism](../../base/pairs/cobordism.md) is a strict [pair](../../base/pairs/poincare-pair.md) with boundary $(C\oplus C',\phi\oplus(-\phi'))$; bounded complexes have [finitely many nonzero chain objects](../../base/complexes/finite-bounded.md), so the products are defined. [Product of a pair with the line](../products/product-with-line.md) gives a strict pair with boundary $((C\oplus C')\otimes\Lambda,(\phi\oplus(-\phi'))\otimes\lambda)$. The isomorphism $(C\oplus C')\otimes\Lambda\cong C\otimes\Lambda\oplus C'\otimes\Lambda$ of [Products distribute over sums](../products/product-sum.md) carries $(\phi\oplus(-\phi'))\otimes\lambda$ to $\phi\otimes\lambda\oplus(-\phi')\otimes\lambda$, and $(-\phi')\otimes\lambda=-(\phi'\otimes\lambda)$ by [additivity in the first structure](../products/bookkeeping/product-additive-left.md). By [Pair transport](../../base/pairs/pair-transport.md) along its inverse, using that [pushforward preserves composition](../../base/complexes/functors/push-comp.md) and [identities](../../base/complexes/functors/push-id.md), the product is a cobordism from $t$ of $C$ to $t$ of $C'$. So $t$ is well defined on cobordism classes.
3. Additivity. The chosen [sum](../../base/pairs/poincare-sum.md) of $(C,\phi)$ and $(C',\phi')$ is identified with $(C\oplus C',\phi\oplus\phi')$. Then the same isomorphism, for $\phi$ and $\phi'$, with $\chi=0$ in [Homotopy-isometry invariance](../../base/groups/homotopy-isometry-invariance.md), gives $t([C,\phi]+[C',\phi'])=t[C,\phi]+t[C',\phi']$ for the [sum](../../base/pairs/poincare-sum.md) of Poincaré complexes.

## Sources

- [Ranicki 1992, §17](../../../../../sources/paper/ranicki-1992.md) [U]
- New: well-definedness from the product lemmas.

## Depends on

- [Small Q-linear category with strict duality](../../base/categories/duality-category.md)
- [Iterated bounded categories](../../bounded/categories/iterated-bounded-category.md)
- [The projective L-group](../../base/groups/projective-l-group.md)
- [Group structure on L](../../base/groups/l-group-add.md)
- [Idempotent completion with duality](../../base/categories/karoubi-duality.md)

## Proof depends on

- [L-group](../../base/groups/l-group.md)
- [Cobordism](../../base/pairs/cobordism.md)
- [Strict symmetric Poincaré complex](../../base/pairs/symmetric-poincare-complex.md)
- [Strict Poincaré pair](../../base/pairs/poincare-pair.md)
- [The sum of two Poincaré complexes](../../base/pairs/poincare-sum.md)
- [Structure complex](../../base/complexes/structure-complex.md)
- [Pushforward of structures](../../base/complexes/structure-push.md)
- [Sum of structured complexes](../../base/complexes/sum-of-complexes.md)
- [Duality pairings](../products/duality-pairing.md)
- [Box product on iterated bounded categories](../products/box-pairing-pow.md)
- [Tensor product of complexes](../products/complex-product.md)
- [External product of structures](../products/external-product.md)
- [The symmetric line](../products/symmetric-line.md)
- [Structure of the symmetric line](../products/symmetric-line-structure.md)
- [Product of a complex with the line](transition-complex.md)
- [Product of a pair with the line](../products/product-with-line.md)
- [Pair transport](../../base/pairs/pair-transport.md)
- [Homotopy-isometry invariance](../../base/groups/homotopy-isometry-invariance.md)
- [Products distribute over sums](../products/product-sum.md)
- [External products are additive in the first structure](../products/bookkeeping/product-additive-left.md)
- [Bounded complexes have finitely many nonzero chain objects](../../base/complexes/finite-bounded.md)
- [Pushforward preserves composition](../../base/complexes/functors/push-comp.md)
- [Pushforward preserves identities](../../base/complexes/functors/push-id.md)
- [A duality category has binary direct sums](../../base/categories/sums/dual-binary-biproducts.md)
- [The bounded category $C_\mathbb Z(A)$](../../bounded/categories/bounded-category.md)
- [The induced duality on $C_\mathbb Z(A)$](../../bounded/categories/bounded-duality.md)
- [Based vector spaces](../products/based-vector-spaces.md)
- [The category of based ℚ-vector spaces](../products/bookkeeping/based-category.md)
- [Tensor product of chain maps](../products/bookkeeping/product-map.md)
