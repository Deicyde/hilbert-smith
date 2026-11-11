---
article_id: af_d13ab21d8e8275dec9fea023
declaration: def
origin: background
---

# Decorated transition

Let $\mathcal U\subset\mathcal A$ be an involution-invariant Karoubi filtration, $j\ge0$ and $m\in\mathbb Z$. The *decorated transition*
$$t^{\mathrm{im}}:L^p_m(C_{\mathbb Z^j}(\mathcal A/\mathcal U))\to L^{\mathrm{im}}_{m+1}(C_{\mathbb Z^{j+1}}\mathcal A/C_{\mathbb Z^{j+1}}\mathcal U),\qquad[C,\phi]\mapsto\big[e_{j+1}^{-1}(C\otimes\Lambda),\ (e_{j+1}^{-1})_\%(\phi\otimes\lambda)\big],$$
is a well-defined homomorphism. Here $e_{j+1}$ is the isomorphism of [Iterated bounded quotients](../../bounded/categories/iterated-bounded-quotient.md), applied through its Karoubi extension.

*Proof sketch.*
1. Complexes. $(C\otimes\Lambda,\phi\otimes\lambda)$ is a strict Poincaré complex ([Transition map](transition-map.md), step 1), and the strict duality functor $e_{j+1}^{-1}$ carries it to one, as in [Induced homomorphism](../../base/groups/induced-map.md). Its chain objects are decorated by [Products with the line are decorated](line-product-decorated.md), so it is a complex in the duality category $\mathrm{Dec}$ of [Decorated objects](../decorations/decorated-object.md).
2. Cobordisms. A cobordism between $C$ and $C'$ gives, as in [Transition map](transition-map.md) step 2, a cobordism whose chain objects are those of products with $\Lambda$. After $e_{j+1}^{-1}$ they are decorated, by the same lemma. So the class does not depend on the representative.
3. Additivity. The canonical isomorphism $(C\oplus C')\otimes\Lambda\cong C\otimes\Lambda\oplus C'\otimes\Lambda$ carries structures exactly. [Homotopy-isometric complexes are cobordant](../../base/pairs/cylinder-cobordism.md), with $\mathcal P$ the decorated objects (closed under sums and duals) and $\chi=0$, gives a cobordism whose chain objects are decorated.

## Sources

- [Ranicki 1992, §17, transfer of decorations along the line](../../../../../sources/paper/ranicki-1992.md) [U]
- New: decoration checked object by object.

## Depends on

- [Transition map](transition-map.md)
- [Decorated quotient L-group](../decorations/decorated-l-group.md)
- [Decorated objects](../decorations/decorated-object.md)
- [Iterated bounded quotients](../../bounded/categories/iterated-bounded-quotient.md)

## Proof depends on

- [Transition map](transition-map.md)
- [Products with the line are decorated](line-product-decorated.md)
- [Induced homomorphism](../../base/groups/induced-map.md)
- [Duality functors carry Poincaré complexes](../../base/pairs/functor-poincare.md)
- [Duality functors carry pairs to pairs](../../base/pairs/functor-pair.md)
- [Homotopy-isometric complexes are cobordant](../../base/pairs/cylinder-cobordism.md)
