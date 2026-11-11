---
article_id: af_b045e4a159e1df5563ca2215
declaration: def
origin: background
statement: formalized
lean: HSP.DualFunctor.dualCxIso
---

# Duality functors and dual complexes

Let $(F,\xi):\mathcal B\to\mathcal B'$ be a [duality functor](../../categories/duality-functor.md), $C$ a complex in $\mathcal B$ and $k\in\mathbb Z$. The maps $\xi^{-1}_{C_{k-r}}:(FC_{k-r})^*\to F(C_{k-r}^*)$ form an isomorphism of complexes
$$\xi^{-1}:(FC)^{k-*}\cong F(C^{k-*})$$
between the [dual complex](../dual-complex.md) of the [image](functor-complex.md) and the image of the dual complex: they commute with the differentials by naturality of $\xi$, the signs being the same on both sides.

## Sources

- New: direct from the definitions.

## Depends on

- [Duality functor](../../categories/duality-functor.md)
- [Image of a complex under a duality functor](functor-complex.md)
- [Dual complex](../dual-complex.md)
