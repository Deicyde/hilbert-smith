---
article_id: af_78d3a49ee3d1dcfbdbac21df
declaration: structure
origin: background
statement: formalized
lean: HSP.DualFunctor.UnitaryIso
---

# Unitary natural isomorphism

Let $(F,\xi),(G,\zeta):\mathcal A\to\mathcal B$ be [duality functors](duality-functor.md) between [duality categories](duality-category.md). A *unitary natural isomorphism* $F\cong G$ consists of

- a natural isomorphism $\eta:F\cong G$ of the underlying functors, and
- the unitarity condition $\eta_M^*\circ\zeta_M\circ\eta_{M^*}=\xi_M$ as maps $F(M^*)\to(FM)^*$, for every object $M$ of $\mathcal A$.

## Sources

- [Ranicki 1992, §1](../../../../../sources/paper/ranicki-1992.md) [U]

## Depends on

- [Small Q-linear category with strict duality](duality-category.md)
- [Duality functor](duality-functor.md)
