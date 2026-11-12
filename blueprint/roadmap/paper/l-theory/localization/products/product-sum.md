---
article_id: af_dd05b1b060d97352bc06df46
declaration: lemma
origin: background
statement: formalized
lean: HSP.cxProd_sum_iso
proof: formalized
---

# Products distribute over sums

Let $(\boxtimes,\kappa):\mathcal B\times\mathcal E\to\mathcal B''$ be a [duality pairing](duality-pairing.md), let $C$, $C'$ be complexes in $\mathcal B$ and $E$ a complex in $\mathcal E$, each with all but finitely many chain objects zero objects, and let $\phi\in M(C)_m$, $\phi'\in M(C')_m$ and $\theta\in M(E)_n$. There is an isomorphism of complexes
$$(C\oplus C')\otimes E\cong C\otimes E\oplus C'\otimes E$$
of [tensor products](complex-product.md) carrying $(\phi\oplus\phi')\otimes\theta$ to $\phi\otimes\theta\oplus\phi'\otimes\theta$, for the [sums of structures](../../base/complexes/sum-of-complexes.md) and [external products](external-product.md).

*Proof sketch.* The inverse isomorphism has components the [tensor products of chain maps](bookkeeping/product-map.md) $i\otimes1$ and $i'\otimes1$ for the inclusions $i$, $i'$ of $C\oplus C'$; its inverse has components $p\otimes1$ and $p'\otimes1$ for the projections. These are inverse by [functoriality](bookkeeping/product-map-comp.md) of $\otimes$ on chain maps, $\otimes$ of [identities](bookkeeping/product-map-id.md) and additivity of $\otimes$ in the first map. By [Pushforward of products](product-push.md), $(i\otimes1)_\%(\phi\otimes\theta)=i_\%\phi\otimes\theta$, and likewise for $i'$. Since $\phi\oplus\phi'=i_\%\phi+i'_\%\phi'$, [additivity of external products](bookkeeping/product-additive-left.md) gives the claim.

## Sources

- New: the canonical isomorphism, split out of the transition map.

## Depends on

- [Duality pairings](duality-pairing.md)
- [Tensor product of complexes](complex-product.md)
- [External product of structures](external-product.md)
- [Sum of complexes](../../base/complexes/sum-of-complexes.md)
- [Pushforward of structures](../../base/complexes/structure-push.md)

## Proof depends on

- [Pushforward of products](product-push.md)
- [Tensor product of chain maps](bookkeeping/product-map.md)
- [Tensor products of chain maps compose](bookkeeping/product-map-comp.md)
- [Tensor product of identities](bookkeeping/product-map-id.md)
- [External products are additive in the first structure](bookkeeping/product-additive-left.md)
- [Pushforward preserves composition](../../base/complexes/functors/push-comp.md)
- [Pushforward preserves identities](../../base/complexes/functors/push-id.md)
