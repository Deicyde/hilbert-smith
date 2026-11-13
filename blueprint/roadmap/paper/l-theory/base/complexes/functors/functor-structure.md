---
article_id: af_c1582f91e641b04b53d3782f
declaration: def
origin: background
statement: formalized
lean: HSP.DualFunctor.mapStructure
---

# Image of structures under a duality functor

Let $(F,\xi):\mathcal B\to\mathcal B'$ be a [duality functor](../../categories/duality-functor.md) and $C$ a complex in $\mathcal B$, with [image](functor-complex.md) $FC$. For each $n$, the map
$$F_\%:M(C)_n\to M(FC)_n,\qquad (F_\%\phi)_{r,s}=F(\phi_{r,s})\circ\xi^{-1}_{C_s}:(FC_s)^*\to F(C_s^*)\to FC_r,$$
on the [structure complexes](../structure-complex.md) is $\mathbb Q$-linear, since $F$ is.

## Sources

- New: direct from the definitions.

## Depends on

- [Duality functor](../../categories/duality-functor.md)
- [Image of a complex under a duality functor](functor-complex.md)
- [Structure complex](../structure-complex.md)
- [Small Q-linear category with strict duality](../../categories/duality-category.md)
