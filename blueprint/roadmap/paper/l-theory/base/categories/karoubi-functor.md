---
article_id: af_6ed7cc0fd0a48b96f41bd89e
declaration: def
origin: background
statement: formalized
lean: HSP.DualFunctor.kar
---

# Completion of a duality functor

A duality functor $(F,\xi):\mathcal A\to\mathcal B$ induces $\mathrm{Kar}\,F:(M,e)\mapsto(FM,Fe)$ with $\xi_{(M,e)}=\xi_M\circ F(e^*)$. This is a duality functor. It is [strict if $F$ is](duality-functors/karoubi-functor-strict.md).

*Proof sketch.* $F(e^*)$ is idempotent and commutes past $\xi$ by naturality, so $\xi_M F(e^*)$ is a morphism of the completion with inverse $F(e^*)\xi_M^{-1}$. Naturality and $(\xi_{(M,e)})^*=\xi_{(M,e)^*}$ follow from those of $\xi$ together with $e^2=e$.

## Sources

- [Ranicki 1992, §1](../../../../../sources/paper/ranicki-1992.md) [U]

## Depends on

- [Idempotent completion with duality](karoubi-duality.md)
- [Duality functor](duality-functor.md)
- [Small Q-linear category with strict duality](duality-category.md)
