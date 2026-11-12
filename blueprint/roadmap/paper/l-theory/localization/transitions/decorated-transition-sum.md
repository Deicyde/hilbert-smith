---
article_id: af_66073425b52767036e3b4ef8
declaration: lemma
origin: background
statement: formalized
lean: HSP.decTransitionCx_sum
proof: formalized
---

# The decorated transition is additive

Let $\mathcal U\subset\mathcal A$ be an involution-invariant Karoubi filtration and $j\ge0$. For strict $m$-dimensional symmetric Poincaré complexes $(C,\phi)$ and $(C',\phi')$ in $\operatorname{Kar}C_{\mathbb Z^j}(\mathcal A/\mathcal U)$, the [decorated product with the line](decorated-line-product.md) of $(C\oplus C',\phi\oplus\phi')$ has the class of the [sum](../../base/pairs/poincare-sum.md) of the decorated products of $(C,\phi)$ and $(C',\phi')$ in the [L-group](../../base/groups/l-group.md) $L_{m+1}(\mathrm{Dec}(C_{\mathbb Z^{j+1}}\mathcal A/C_{\mathbb Z^{j+1}}\mathcal U))=L^{\mathrm{im}}_{m+1}(C_{\mathbb Z^{j+1}}\mathcal A/C_{\mathbb Z^{j+1}}\mathcal U)$.

*Proof sketch.* By [Products distribute over sums](../products/product-sum.md), composed with the identification of the chosen sum with $C\oplus C'$, there is an isomorphism $(C\oplus C')\otimes\Lambda\cong C\otimes\Lambda\oplus C'\otimes\Lambda$ carrying $(\phi\oplus\phi')\otimes\lambda$ to $\phi\otimes\lambda\oplus\phi'\otimes\lambda$. Applying $e_{j+1}^{-1}$, which is additive, gives an isomorphism onto the sum of the images, carrying the structures ([Duality functors commute with pushforward](../../base/complexes/functor-push.md)). All chain objects involved are decorated, so [Sums in a full subcategory](../decorations/subcategory-sum.md) gives the claim.

## Sources

- New: step 3 of the decorated transition, split out.

## Depends on

- [The sum of two Poincaré complexes](../../base/pairs/poincare-sum.md)
- [Decorated product with the line](decorated-line-product.md)
- [L-group](../../base/groups/l-group.md)
- [Strict symmetric Poincaré complex](../../base/pairs/symmetric-poincare-complex.md)
- [Additive subcategory closed under duality](../../base/categories/dual-additive-subcategory.md)
- [Small Q-linear category with strict duality](../../base/categories/duality-category.md)
- [Quotient by a subcategory](../../base/categories/filtration-quotient.md)
- [Involution-invariant Karoubi filtration](../../base/categories/karoubi-filtration.md)
- [Iterated bounded categories](../../bounded/categories/iterated-bounded-category.md)

## Proof depends on

- [Products distribute over sums](../products/product-sum.md)
- [Duality functors commute with pushforward](../../base/complexes/functor-push.md)
- [Sums in a full subcategory](../decorations/subcategory-sum.md)
- [Group structure on L](../../base/groups/l-group-add.md)
- [Inclusion of a dual-closed subcategory](../../base/categories/subcategory-inclusion.md)
- [Completion of a duality functor](../../base/categories/karoubi-functor.md)
- [Image of structures under a duality functor](../../base/complexes/functors/functor-structure.md)
- [Bounded complexes have finitely many nonzero chain objects](../../base/complexes/finite-bounded.md)
- [Structure complex](../../base/complexes/structure-complex.md)
- [Pushforward of structures](../../base/complexes/structure-push.md)
- [Pushforward preserves composition](../../base/complexes/functors/push-comp.md)
- [Pushforward preserves identities](../../base/complexes/functors/push-id.md)
- [Duality functors preserve sums of structures](../../base/complexes/functors/functor-structure-sum.md)
- [Tensor product of chain maps](../products/bookkeeping/product-map.md)
- [Tensor products of chain maps compose](../products/bookkeeping/product-map-comp.md)
- [Tensor product of identities](../products/bookkeeping/product-map-id.md)
- [Pushforward of products](../products/product-push.md)
- [Tensor product of complexes](../products/complex-product.md)
- [External product of structures](../products/external-product.md)
- [Duality functors carry Poincaré complexes](../../base/pairs/functor-poincare.md)
- [Complexes in a full subcategory](../decorations/complex-in-subcategory.md)
- [Decorated objects of the completed quotient](../decorations/decorated-predicate.md)
- [Product of a complex with the line](transition-complex.md)
- [Iterated bounded quotients](../../bounded/categories/iterated-bounded-quotient.md)
- [Iterated bounded subcategories](../../bounded/categories/iterated-bounded-sub.md)
- [Box product on iterated bounded categories](../products/box-pairing-pow.md)
- [The symmetric line](../products/symmetric-line.md)
- [Structure of the symmetric line](../products/symmetric-line-structure.md)
