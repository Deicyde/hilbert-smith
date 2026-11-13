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
- [Additive subcategory closed under duality](../../base/categories/dual-additive-subcategory.md)
- [Small Q-linear category with strict duality](../../base/categories/duality-category.md)
- [Quotient by a subcategory](../../base/categories/filtration-quotient.md)
- [Involution-invariant Karoubi filtration](../../base/categories/karoubi-filtration.md)
- [Strict symmetric Poincaré complex](../../base/pairs/symmetric-poincare-complex.md)
- [Iterated bounded categories](../../bounded/categories/iterated-bounded-category.md)
- [Duality category of a dual-closed subcategory](../../base/categories/dual-subcategory.md)
- [Idempotent completion with duality](../../base/categories/karoubi-duality.md)
- [Iterated bounded subcategories are closed under sums and duals](../../bounded/categories/iterated-bounded-sub-additive.md)
- [Iterated bounded subcategories](../../bounded/categories/iterated-bounded-sub.md)
- [Decorated objects are closed under sums and duals](../decorations/decorated-closure.md)
- [Decorated objects](../decorations/decorated-object.md)
- [Decorated objects of the completed quotient](../decorations/decorated-predicate.md)

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
- [Inclusion of a dual-closed subcategory](../../base/categories/subcategory-inclusion.md)
- [Completion of a duality functor](../../base/categories/karoubi-functor.md)
- [Image of structures under a duality functor](../../base/complexes/functors/functor-structure.md)
- [Bounded complexes have finitely many nonzero chain objects](../../base/complexes/finite-bounded.md)
- [Pushforward preserves composition](../../base/complexes/functors/push-comp.md)
- [Pushforward preserves identities](../../base/complexes/functors/push-id.md)
- [Structure complex](../../base/complexes/structure-complex.md)
- [Pushforward of structures](../../base/complexes/structure-push.md)
- [Sum of structured complexes](../../base/complexes/sum-of-complexes.md)
- [Strict Poincaré pair](../../base/pairs/poincare-pair.md)
- [Iterated bounded quotients](../../bounded/categories/iterated-bounded-quotient.md)
- [Tensor product of chain maps](../products/bookkeeping/product-map.md)
- [Tensor products of chain maps compose](../products/bookkeeping/product-map-comp.md)
- [Tensor product of identities](../products/bookkeeping/product-map-id.md)
- [Box product on iterated bounded categories](../products/box-pairing-pow.md)
- [Tensor product of complexes](../products/complex-product.md)
- [External product of structures](../products/external-product.md)
- [The symmetric line](../products/symmetric-line.md)
- [Structure of the symmetric line](../products/symmetric-line-structure.md)
- [Product of a complex with the line](transition-complex.md)
- [Duality functor](../../base/categories/duality-functor.md)
- [Strict duality functor](../../base/categories/duality-functors/strict-duality-functor.md)
- [A duality category has binary direct sums](../../base/categories/sums/dual-binary-biproducts.md)
- [Image of a complex under a duality functor](../../base/complexes/functors/functor-complex.md)
- [The bounded category $C_\mathbb Z(A)$](../../bounded/categories/bounded-category.md)
- [The induced duality on $C_\mathbb Z(A)$](../../bounded/categories/bounded-duality.md)
- [Isomorphism classes of objects](../../bounded/categories/classes/iso-classes.md)
- [The class of an object in $K_0$](../../bounded/categories/classes/k-zero-class.md)
- [$K_0$ of an idempotent completion](../../bounded/categories/k-zero.md)
- [Based vector spaces](../products/based-vector-spaces.md)
- [The category of based ℚ-vector spaces](../products/bookkeeping/based-category.md)
- [Duality pairings](../products/duality-pairing.md)
