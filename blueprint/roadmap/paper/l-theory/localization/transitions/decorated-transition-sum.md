---
article_id: af_66073425b52767036e3b4ef8
declaration: lemma
origin: background
statement: formalized
lean: HSP.decTransitionCx_sum
proof: formalized
---

# The decorated transition is additive

Let $\mathcal U\subset\mathcal A$ be an involution-invariant Karoubi filtration and $j\ge0$. For strict $m$-dimensional symmetric Poincaré complexes $(C,\phi)$ and $(C',\phi')$ in $\operatorname{Kar}C_{\mathbb Z^j}(\mathcal A/\mathcal U)$, the [decorated product with the line](decorated-line-product.md) of $(C\oplus C',\phi\oplus\phi')$ has the class of the sum of the decorated products of $(C,\phi)$ and $(C',\phi')$ in $L^{\mathrm{im}}_{m+1}(C_{\mathbb Z^{j+1}}\mathcal A/C_{\mathbb Z^{j+1}}\mathcal U)$.

*Proof sketch.* By [Products distribute over sums](../products/product-sum.md), composed with the identification of the chosen sum with $C\oplus C'$, there is an isomorphism $(C\oplus C')\otimes\Lambda\cong C\otimes\Lambda\oplus C'\otimes\Lambda$ carrying $(\phi\oplus\phi')\otimes\lambda$ to $\phi\otimes\lambda\oplus\phi'\otimes\lambda$. Applying $e_{j+1}^{-1}$, which is additive, gives an isomorphism onto the sum of the images, carrying the structures ([Duality functors commute with pushforward](../../base/complexes/functor-push.md)). All chain objects involved are decorated, so [Sums in a full subcategory](../decorations/subcategory-sum.md) gives the claim.

## Sources

- New: step 3 of the decorated transition, split out.

## Depends on

- [The sum of two Poincaré complexes](../../base/pairs/poincare-sum.md)
- [Decorated product with the line](decorated-line-product.md)
- [Decorated quotient L-group](../decorations/decorated-l-group.md)
- [Group structure on L](../../base/groups/l-group-add.md)
- [Inclusion of a dual-closed subcategory](../../base/categories/subcategory-inclusion.md)

## Proof depends on

- [Products distribute over sums](../products/product-sum.md)
- [Duality functors commute with pushforward](../../base/complexes/functor-push.md)
- [Sums in a full subcategory](../decorations/subcategory-sum.md)
- [Bounded complexes have finitely many nonzero chain objects](../../base/complexes/finite-bounded.md)
