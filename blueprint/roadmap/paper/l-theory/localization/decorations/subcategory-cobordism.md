---
article_id: af_5231585879ee9f88dd593690
declaration: lemma
origin: background
statement: formalized
lean: HSP.SymPoincare.cobordant_of_pair
proof: formalized
---

# Cobordisms in a full subcategory

Let $\mathcal P\subset\mathcal B$ be a full additive subcategory of a duality category, closed under duality and hence a duality category with the restricted duality, and let $(C,\phi)$, $(C',\phi')$ be strict $k$-dimensional symmetric Poincaré complexes in $\mathcal P$. Let $(f:E\to D,\delta\phi,\psi)$ be a strict $(k+1)$-dimensional [Poincaré pair](../../base/pairs/poincare-pair.md) in $\mathcal B$ such that every chain object of $D$ lies in $\mathcal P$, and let $u:C\oplus C'\cong E$ be an isomorphism of complexes in $\mathcal B$ carrying $\phi\oplus(-\phi')$ to $\psi$. Then $(C,\phi)$ and $(C',\phi')$ are [cobordant](../../base/pairs/cobordism.md) in $\mathcal P$.

*Proof sketch.* Let $(Z,\zeta)$ be a [sum](../../base/pairs/sum-of-poincare.md) in $\mathcal P$ of $(C,\phi)$ and the [negative](../../base/pairs/poincare-neg.md) $(C',-\phi')$ of $(C',\phi')$. The inclusion preserves sums, so $u$ gives an isomorphism from the image of $Z$ onto $E$ carrying $\zeta$ to $\psi$ ([Duality functors preserve sums of structures](../../base/complexes/functors/functor-structure-sum.md)), and [Pair transport](../../base/pairs/pair-transport.md) gives a pair in $\mathcal B$ with boundary the image of $(Z,\zeta)$ and the same $D$ and $\delta\phi$. Its data lift to $\mathcal P$: the boundary is $(Z,\zeta)$ itself, $D$ and $\delta\phi$ lift because all chain objects of $D$ lie in $\mathcal P$, and the boundary equation and $T\delta\phi=\delta\phi$ hold in $\mathcal P$ because they hold after the inclusion, which is faithful ([Images of structures commute with the boundary, T and the duality map](../../base/complexes/functors/functor-structure-laws.md), [Duality functors commute with pushforward](../../base/complexes/functor-push.md)). The inclusion carries the mapping cone and the pair map of the lifted pair to those of the pair in $\mathcal B$ ([Duality functors and mapping cones](../../base/complexes/functors/functor-cone.md), [Duality functors and pair maps](../../base/complexes/functors/functor-pair-map.md)), so the chain homotopy equivalence lifts ([Lifting homotopy equivalences to a full subcategory](../../base/complexes/functors/lift-homotopy-equiv.md)). The lifted pair is a cobordism between $(C,\phi)$ and $(C',\phi')$.

## Sources

- New: bookkeeping for decorated L-groups.

## Depends on

- [Inclusion of a dual-closed subcategory](../../base/categories/subcategory-inclusion.md)
- [Strict Poincaré pair](../../base/pairs/poincare-pair.md)
- [Cobordism](../../base/pairs/cobordism.md)
- [Sum of structured complexes](../../base/complexes/sum-of-complexes.md)
- [Image of a complex under a duality functor](../../base/complexes/functors/functor-complex.md)
- [Image of structures under a duality functor](../../base/complexes/functors/functor-structure.md)
- [Pushforward of structures](../../base/complexes/structure-push.md)
- [Strict symmetric Poincaré complex](../../base/pairs/symmetric-poincare-complex.md)
- [Additive subcategory closed under duality](../../base/categories/dual-additive-subcategory.md)
- [Small Q-linear category with strict duality](../../base/categories/duality-category.md)

## Proof depends on

- [Duality functors preserve sums of structures](../../base/complexes/functors/functor-structure-sum.md)
- [Pair transport](../../base/pairs/pair-transport.md)
- [Images of structures commute with the boundary, T and the duality map](../../base/complexes/functors/functor-structure-laws.md)
- [Duality functors commute with pushforward](../../base/complexes/functor-push.md)
- [Duality functors and mapping cones](../../base/complexes/functors/functor-cone.md)
- [Duality functors and pair maps](../../base/complexes/functors/functor-pair-map.md)
- [Lifting homotopy equivalences to a full subcategory](../../base/complexes/functors/lift-homotopy-equiv.md)
- [Pushforward preserves composition](../../base/complexes/functors/push-comp.md)
- [Pushforward preserves identities](../../base/complexes/functors/push-id.md)
- [Mapping cone](../../base/complexes/cone.md)
- [Dual complex](../../base/complexes/dual-complex.md)
- [Duality functors and dual complexes](../../base/complexes/functors/functor-dual-iso.md)
- [Structure complex](../../base/complexes/structure-complex.md)
- [Pair map](../../base/pairs/pair-map.md)
- [Sums of Poincaré complexes](../../base/pairs/sum-of-poincare.md)
- [Negative of a Poincaré complex](../../base/pairs/poincare-neg.md)
