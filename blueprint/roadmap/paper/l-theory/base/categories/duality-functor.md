---
article_id: af_ca66912614a1381bc1c3d53d
declaration: structure
origin: background
statement: formalized
lean: HSP.DualFunctor
---

# Duality functor

A *duality functor* $(F,\xi):\mathcal A\to\mathcal B$ between duality categories is a $\mathbb Q$-linear (in particular additive) functor $F$ with a natural isomorphism $\xi_M:F(M^*)\to F(M)^*$, that is $\xi_M\circ F(f^*)=F(f)^*\circ\xi_N$ for $f:M\to N$, such that $(\xi_M)^*=\xi_{M^*}$, where both sides are read as maps $F(M)\to F(M^*)^*$ through $F(M)^{**}=F(M)=F(M^{**})$. It is *strict* if $\xi=\mathrm{id}$: $F(M^*)=F(M)^*$ and $\xi_M$ is the identity for every $M$. The identity duality functor has $\xi=\mathrm{id}$. Composition: $\xi^{GF}_M=\zeta_{FM}\circ G(\xi_M)$.

## Sources

- [Ranicki 1992, §1](../../../../../sources/paper/ranicki-1992.md) [U]

## Depends on

- [Small Q-linear category with strict duality](duality-category.md)
