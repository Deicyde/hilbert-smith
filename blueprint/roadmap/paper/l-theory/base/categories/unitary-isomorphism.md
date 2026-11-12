---
article_id: af_78d3a49ee3d1dcfbdbac21df
declaration: structure
origin: background
statement: formalized
lean: HSP.DualFunctor.UnitaryIso
---

# Unitary natural isomorphism

A natural isomorphism $\eta:F\cong G$ of duality functors $(F,\xi),(G,\zeta):\mathcal A\to\mathcal B$ is *unitary* if $\eta_M^*\circ\zeta_M\circ\eta_{M^*}=\xi_M$ for every $M$. The identity of a duality functor is unitary, and if $\eta:F\cong G$ and $\theta:G\cong H$ are unitary then so is $\theta\circ\eta:F\cong H$, since $(\theta\eta)_M^*\,\omega_M\,(\theta\eta)_{M^*}=\eta_M^*(\theta_M^*\omega_M\theta_{M^*})\eta_{M^*}=\eta_M^*\zeta_M\eta_{M^*}=\xi_M$ for the duality isomorphism $\omega$ of $H$.

## Sources

- [Ranicki 1992, §1](../../../../../sources/paper/ranicki-1992.md) [U]

## Depends on

- [Duality functor](duality-functor.md)
