---
article_id: af_082a1ce26b6e7396139f1cba
declaration: lemma
origin: background
statement: formalized
lean: HSP.decTransitionCx_cobordant
---

# The decorated transition respects cobordism

Let $\mathcal U\subset\mathcal A$ be an involution-invariant Karoubi filtration and $j\ge0$. If $(C,\phi)$ and $(C',\phi')$ are cobordant strict $m$-dimensional symmetric Poincaré complexes in $\operatorname{Kar}C_{\mathbb Z^j}(\mathcal A/\mathcal U)$, then their [decorated products with the line](decorated-line-product.md) are cobordant in $\mathrm{Dec}(C_{\mathbb Z^{j+1}}\mathcal A/C_{\mathbb Z^{j+1}}\mathcal U)$.

*Proof sketch.* A cobordism between $C$ and $C'$ gives, as in [Transition map](transition-map.md) step 2, a cobordism whose chain objects are those of products with $\Lambda$ ([Product of a pair with the line](../products/product-with-line.md)). After $e_{j+1}^{-1}$ ([Duality functors carry pairs to pairs](../../base/pairs/functor-pair.md)) they are decorated, by [Products with the line are decorated](line-product-decorated.md), so it is a cobordism in $\mathrm{Dec}$.

## Sources

- New: step 2 of the decorated transition, split out.

## Depends on

- [Decorated product with the line](decorated-line-product.md)
- [Cobordism](../../base/pairs/cobordism.md)

## Proof depends on

- [Transition map](transition-map.md)
- [Product of a pair with the line](../products/product-with-line.md)
- [Products with the line are decorated](line-product-decorated.md)
- [Duality functors carry pairs to pairs](../../base/pairs/functor-pair.md)
