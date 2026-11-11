---
article_id: af_1d838c5fbf572a8c91166c59
declaration: def
origin: background
statement: formalized
lean: HSP.decTransitionCx
---

# Decorated product with the line

Let $\mathcal U\subset\mathcal A$ be an involution-invariant Karoubi filtration, $j\ge0$, and let $(C,\phi)$ be a strict $m$-dimensional symmetric Poincaré complex in $\operatorname{Kar}C_{\mathbb Z^j}(\mathcal A/\mathcal U)$. Then
$$\big(e_{j+1}^{-1}(C\otimes\Lambda),\ (e_{j+1}^{-1})_\%(\phi\otimes\lambda)\big)$$
is a strict $(m+1)$-dimensional symmetric Poincaré complex in the duality category $\mathrm{Dec}(C_{\mathbb Z^{j+1}}\mathcal A/C_{\mathbb Z^{j+1}}\mathcal U)$ of [decorated objects](../decorations/decorated-object.md). Here $e_{j+1}$ is the isomorphism of [Iterated bounded quotients](../../bounded/categories/iterated-bounded-quotient.md), applied through its Karoubi extension.

*Proof sketch.* $(C\otimes\Lambda,\phi\otimes\lambda)$ is a strict Poincaré complex ([Product of a complex with the line](transition-complex.md)), and the strict duality functor $e_{j+1}^{-1}$ carries it to one ([Duality functors carry Poincaré complexes](../../base/pairs/functor-poincare.md)). Its chain objects are decorated by [Products with the line are decorated](line-product-decorated.md), so it is a complex in $\mathrm{Dec}$ by [Complexes in a full subcategory](../decorations/complex-in-subcategory.md).

## Sources

- New: step 1 of the decorated transition, split out.

## Depends on

- [Decorated objects of the completed quotient](../decorations/decorated-predicate.md)
- [Product of a complex with the line](transition-complex.md)
- [Products with the line are decorated](line-product-decorated.md)
- [Decorated objects](../decorations/decorated-object.md)
- [Complexes in a full subcategory](../decorations/complex-in-subcategory.md)
- [Iterated bounded quotients](../../bounded/categories/iterated-bounded-quotient.md)
- [Duality functors carry Poincaré complexes](../../base/pairs/functor-poincare.md)
