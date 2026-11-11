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
is a well-defined homomorphism. For $m=k+j$ it is a homomorphism $L^{\langle -j\rangle}_k(\mathcal A)\to L^{\langle -j-1\rangle}_k(\mathcal A)$.

*Proof sketch.*
1. Complexes. $(C\otimes\Lambda,\phi\otimes\lambda)$ is a strict $(m+1)$-dimensional symmetric Poincaré complex: its chain objects are zero objects outside $[0,m+1]$; $T(\phi\otimes\lambda)=\phi\otimes\lambda$ and $\partial(\phi\otimes\lambda)=0$ by [Products commute with T](../products/product-involution.md) and the [Leibniz rule](../products/product-leibniz.md); and $(\phi\otimes\lambda)_\natural=(\phi_\natural\otimes\lambda_\natural)\circ\Xi$ ([Duality map of a product](../products/product-duality-map.md)) is an equivalence by [Tensor products of equivalences](../products/product-equivalence.md) and [The line is Poincaré](../products/symmetric-line-poincare.md).
2. Cobordisms. A cobordism is a strict pair with boundary $(C\oplus C',\phi\oplus(-\phi'))$. [Product of a pair with the line](../products/product-with-line.md) gives a strict pair with boundary $((C\oplus C')\otimes\Lambda,(\phi\oplus(-\phi'))\otimes\lambda)$. The canonical isomorphism $(C\oplus C')\otimes\Lambda\cong C\otimes\Lambda\oplus C'\otimes\Lambda$ is assembled from the products of the summand inclusions with $1_\Lambda$, so by [Pushforward of products](../products/product-push.md) and bilinearity of $\boxtimes$ it carries $\phi\otimes\lambda\oplus(-\phi'\otimes\lambda)$ to $(\phi\oplus(-\phi'))\otimes\lambda$. By [Pair transport](../../base/pairs/pair-transport.md) the product is a cobordism from $t$ of $C$ to $t$ of $C'$. So $t$ is well defined on cobordism classes.
3. Additivity. The same canonical isomorphism, with $\chi=0$ in [Homotopy-isometry invariance](../../base/groups/homotopy-isometry-invariance.md), gives $t([C,\phi]+[C',\phi'])=t[C,\phi]+t[C',\phi']$.
4. Stages. $L^{\langle -j\rangle}_k(\mathcal A)=L^p_{k+j}(C_{\mathbb Z^j}\mathcal A)$, and $k+j+1=k+(j+1)$.

## Sources

- [Ranicki 1992, §17](../../../../../sources/paper/ranicki-1992.md) [U]
- New: well-definedness from the product lemmas.

## Depends on

- [L-group](../../base/groups/l-group.md)
- [Group structure on L](../../base/groups/l-group-add.md)
- [Tensor product of complexes](../products/complex-product.md)
- [External product of structures](../products/external-product.md)
- [The symmetric line](../products/symmetric-line.md)
- [Lower L-group](lower-l-group.md)
- [Duals of box products](../products/box-dual.md)

## Proof depends on

- [Products commute with T](../products/product-involution.md)
- [Leibniz rule for products](../products/product-leibniz.md)
- [Duality map of a product](../products/product-duality-map.md)
- [Tensor products of equivalences](../products/product-equivalence.md)
- [The line is Poincaré](../products/symmetric-line-poincare.md)
- [Product of a pair with the line](../products/product-with-line.md)
- [Pair transport](../../base/pairs/pair-transport.md)
- [Pushforward of products](../products/product-push.md)
- [Dual of a tensor product](../products/product-dual-iso.md)
- [Homotopy-isometry invariance](../../base/groups/homotopy-isometry-invariance.md)
