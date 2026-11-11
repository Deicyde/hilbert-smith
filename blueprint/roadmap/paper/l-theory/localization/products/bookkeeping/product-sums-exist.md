---
article_id: af_45956f990c40d992e8367823
declaration: lemma
origin: background
statement: formalized
lean: HSP.DualityPairing.hasMapBifunctor_of_finite
proof: formalized
---

# The sums in a tensor product of complexes exist

Let $(\boxtimes,\kappa):\mathcal B\times\mathcal E\to\mathcal B''$ be a [duality pairing](../duality-pairing.md), and $C$ a complex in $\mathcal B$ and $E$ a complex in $\mathcal E$, each with all but finitely many chain objects zero objects. Then for every $r\in\mathbb Z$ the direct sum $\bigoplus_{p+q=r}C_p\boxtimes E_q$ over all $(p,q)\in\mathbb Z^2$ with $p+q=r$ exists in $\mathcal B''$, as a coproduct.

*Proof sketch.* Only the finitely many summands in the [support](product-support.md) are nonzero ([Summands outside the support vanish](summand-zero.md)). The finite biproduct of those summands, with zero maps from the others, is a coproduct of the whole family, because maps out of a zero object are zero.

## Sources

- New: needed to form the [tensor product of complexes](../complex-product.md).

## Depends on

- [Duality pairings](../duality-pairing.md)
- [Support of a tensor product of complexes](product-support.md)
- [Signs for tensor products of chain complexes](tensor-signs.md)
- [A duality pairing is additive in the first variable](pairing-additive-left.md)
- [A duality pairing is additive in the second variable](pairing-additive-right.md)

## Proof depends on

- [Summands outside the support vanish](summand-zero.md)
