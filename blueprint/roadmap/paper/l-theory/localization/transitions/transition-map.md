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
2. Cobordisms. A cobordism is a strict pair with boundary $(C\oplus C',\phi\oplus(-\phi'))$. [Product of a pair with the line](../products/product-with-line.md) gives a strict pair with boundary $((C\oplus C')\otimes\Lambda,(\phi\oplus(-\phi'))\otimes\lambda)$. The canonical isomorphism $(C\oplus C')\otimes\Lambda\cong C\otimes\Lambda\oplus C'\otimes\Lambda$ is assembled from the products of the summand inclusions with $1_\Lambda$, so by [Pushforward of products](../products/product-push.md) and bilinearity of $\boxtimes$ it carries $\phi\otimes\lambda\oplus(-\phi'\otimes\lambda)$ to $(\phi\oplus(-\phi'))\otimes\lambda$. By [Pair transport](../../base/pairs/pair-transport.md) the product is a cobordism from $t$ of $C$ to $t$ of $C'$. So $t$ is well defined on cobordism classes.
3. Additivity. The same canonical isomorphism, with $\chi=0$ in [Homotopy-isometry invariance](../../base/groups/homotopy-isometry-invariance.md), gives $t([C,\phi]+[C',\phi'])=t[C,\phi]+t[C',\phi']$.

## Sources

- [Ranicki 1992, §17](../../../../../sources/paper/ranicki-1992.md) [U]
- New: well-definedness from the product lemmas.

## Depends on

- [Box product on iterated bounded categories](../products/box-pairing-pow.md)
- [L-group](../../base/groups/l-group.md)
- [Group structure on L](../../base/groups/l-group-add.md)
- [Tensor product of complexes](../products/complex-product.md)
- [External product of structures](../products/external-product.md)
- [The symmetric line](../products/symmetric-line.md)
- [Duals of box products](../products/box-dual.md)
- [Product of a complex with the line](transition-complex.md)
- [Structure of the symmetric line](../products/symmetric-line-structure.md)
- [The projective L-group](../../base/groups/projective-l-group.md)

## Proof depends on

- [Product of a pair with the line](../products/product-with-line.md)
- [Pair transport](../../base/pairs/pair-transport.md)
- [The symmetric line is a symmetric complex](../products/symmetric-line-cycle.md)
- [Pushforward of products](../products/product-push.md)
- [Homotopy-isometry invariance](../../base/groups/homotopy-isometry-invariance.md)
- [Products distribute over sums](../products/product-sum.md)
- [External products are additive in the first structure](../products/bookkeeping/product-additive-left.md)
- [Bounded complexes have finitely many nonzero chain objects](../../base/complexes/finite-bounded.md)
- [Pushforward preserves composition](../../base/complexes/functors/push-comp.md)
- [Pushforward preserves identities](../../base/complexes/functors/push-id.md)
