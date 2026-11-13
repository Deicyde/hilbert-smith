---
article_id: af_b9e0a7cf12cf8484e97f9605
declaration: def
origin: background
statement: formalized
lean: HSP.DualFunctor.mapConeIso
---

# Duality functors and mapping cones

Let $(F,\xi):\mathcal B\to\mathcal B'$ be a [duality functor](../../categories/duality-functor.md) and $f:C\to D$ a chain map. The maps $F(D_r\oplus C_{r-1})\to FD_r\oplus FC_{r-1}$ with components $F(\mathrm{pr}_D)$ and $F(\mathrm{pr}_C)$ are isomorphisms, since $F$ is additive, and they form an isomorphism of complexes
$$\kappa:F(\mathcal C(f))\cong\mathcal C(Ff)$$
from the [image](functor-complex.md) of the [mapping cone](../cone.md) to the mapping cone of the image of $f$: on each summand both differentials are $F$ applied to the same components, with the same signs.

## Sources

- New: direct from the definitions.

## Depends on

- [Duality functor](../../categories/duality-functor.md)
- [Image of a complex under a duality functor](functor-complex.md)
- [Mapping cone](../cone.md)
- [A duality category has binary direct sums](../../categories/sums/dual-binary-biproducts.md)
- [Small Q-linear category with strict duality](../../categories/duality-category.md)
