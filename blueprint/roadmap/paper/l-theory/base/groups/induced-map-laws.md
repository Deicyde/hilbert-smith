---
article_id: af_8b5d05d62331fff058a01a8b
declaration: lemma
origin: bridged
statement: formalized
lean: HSP.SymPoincare.map_cobordant
proof: formalized
---

# Duality functors on cobordism classes

Let $(F,\xi):\mathcal B\to\mathcal B'$ be a [duality functor](../categories/duality-functor.md) and use the [images](../pairs/functor-poincare.md) $(FC,F_\%\phi)$ of strict $k$-dimensional symmetric Poincaré complexes. Then:
1. if $(C,\phi)$ is [cobordant](../pairs/cobordism.md) to $(C',\phi')$, then $(FC,F_\%\phi)$ is cobordant to $(FC',F_\%\phi')$;
2. the image of $(C,\phi)\oplus(C',\phi')$ is cobordant to $(FC,F_\%\phi)\oplus(FC',F_\%\phi')$, with [the sum of two Poincaré complexes](../pairs/poincare-sum.md).

*Proof sketch.* (1) A cobordism goes, by [Duality functors carry pairs to pairs](../pairs/functor-pair.md), to a pair with boundary $(F(C\oplus C'),F_\%(\phi\oplus(-\phi')))$. The canonical isomorphism $u:FC\oplus FC'\cong F(C\oplus C')$ carries $F_\%\phi\oplus(-F_\%\phi')$ to that structure, so it is a cobordism by [Transported pairs are cobordisms](../pairs/transport-cobordism.md) with $s=1$. (2) The isomorphism $u^{-1}$, composed with the identifications of the sums with $C\oplus C'$ and $FC\oplus FC'$, carries the structures exactly, so [Isomorphic Poincaré complexes are cobordant](../pairs/iso-cobordism.md) applies.

## Sources

- New: direct from the definitions

## Depends on

- [Duality functors carry Poincaré complexes](../pairs/functor-poincare.md)
- [The sum of two Poincaré complexes](../pairs/poincare-sum.md)
- [Cobordism](../pairs/cobordism.md)
- [Small Q-linear category with strict duality](../categories/duality-category.md)
- [Duality functor](../categories/duality-functor.md)
- [Strict symmetric Poincaré complex](../pairs/symmetric-poincare-complex.md)

## Proof depends on

- [Duality functors carry pairs to pairs](../pairs/functor-pair.md)
- [Duality functors commute with pushforward](../complexes/functor-push.md)
- [Transported pairs are cobordisms](../pairs/transport-cobordism.md)
- [Isomorphic Poincaré complexes are cobordant](../pairs/iso-cobordism.md)
- [Pushforward preserves composition](../complexes/functors/push-comp.md)
- [Pushforward preserves identities](../complexes/functors/push-id.md)
- [A duality category has binary direct sums](../categories/sums/dual-binary-biproducts.md)
- [Image of a complex under a duality functor](../complexes/functors/functor-complex.md)
- [Image of structures under a duality functor](../complexes/functors/functor-structure.md)
- [Structure complex](../complexes/structure-complex.md)
- [Pushforward of structures](../complexes/structure-push.md)
- [Sum of structured complexes](../complexes/sum-of-complexes.md)
- [Strict Poincaré pair](../pairs/poincare-pair.md)
