---
article_id: af_082a1ce26b6e7396139f1cba
declaration: lemma
origin: background
statement: formalized
lean: HSP.decTransitionCx_cobordant
proof: formalized
---

# The decorated transition respects cobordism

Let $\mathcal U\subset\mathcal A$ be an involution-invariant Karoubi filtration and $j\ge0$. If $(C,\phi)$ and $(C',\phi')$ are cobordant strict $m$-dimensional symmetric Poincaré complexes in $\operatorname{Kar}C_{\mathbb Z^j}(\mathcal A/\mathcal U)$, then their [decorated products with the line](decorated-line-product.md) are cobordant in $\mathrm{Dec}(C_{\mathbb Z^{j+1}}\mathcal A/C_{\mathbb Z^{j+1}}\mathcal U)$.

*Proof sketch.* Let $W=(f:E\to D,\delta\psi,\psi)$ be a cobordism, with an isomorphism $C\oplus C'\cong E$ carrying $\phi\oplus(-\phi')$ to $\psi$. Its [product with the line](../products/product-with-line.md) is a pair $W\otimes\Lambda$ with boundary $(E\otimes\Lambda,\psi\otimes\lambda)$ and codomain $D\otimes\Lambda$, and so is its image under $e_{j+1}^{-1}$ ([Duality functors carry pairs to pairs](../../base/pairs/functor-pair.md)). The chain objects of $e_{j+1}^{-1}(D\otimes\Lambda)$ are decorated, by [Products with the line are decorated](line-product-decorated.md). By [Products distribute over sums](../products/product-sum.md), the functoriality of products ([Pushforward of products](../products/product-push.md)) and additivity of $e_{j+1}^{-1}$ ([Duality functors preserve sums of structures](../../base/complexes/functors/functor-structure-sum.md), [Duality functors commute with pushforward](../../base/complexes/functor-push.md)), the boundary is isomorphic to the sum of the decorated products of $(C,\phi)$ and $(C',-\phi')$, compatibly with the structures, since $(-\phi')\otimes\lambda=-(\phi'\otimes\lambda)$. [Cobordisms in a full subcategory](../decorations/subcategory-cobordism.md) gives the claim.

## Sources

- New: step 2 of the decorated transition, split out.

## Depends on

- [Decorated product with the line](decorated-line-product.md)
- [Cobordism](../../base/pairs/cobordism.md)

## Proof depends on

- [Product of a pair with the line](../products/product-with-line.md)
- [Products with the line are decorated](line-product-decorated.md)
- [Duality functors carry pairs to pairs](../../base/pairs/functor-pair.md)
- [Cobordisms in a full subcategory](../decorations/subcategory-cobordism.md)
- [Products distribute over sums](../products/product-sum.md)
- [Pushforward of products](../products/product-push.md)
- [Duality functors preserve sums of structures](../../base/complexes/functors/functor-structure-sum.md)
- [Duality functors commute with pushforward](../../base/complexes/functor-push.md)
- [External products are additive in the first structure](../products/bookkeeping/product-additive-left.md)
