---
article_id: af_5199d1fa58629c3a1174f570
declaration: def
origin: background
statement: formalized
lean: HSP.DualFunctor.UnitaryIso.refl, HSP.DualFunctor.UnitaryIso.trans
---

# Identity and composite of unitary isomorphisms

Let $(F,\xi),(G,\zeta),(H,\omega):\mathcal A\to\mathcal B$ be [duality functors](../categories/duality-functor.md) between [duality categories](../categories/duality-category.md).

1. The identity natural isomorphism $\mathrm{id}:F\cong F$ is a [unitary natural isomorphism](../categories/unitary-isomorphism.md).
2. If $\eta:F\cong G$ and $\theta:G\cong H$ are unitary natural isomorphisms, then the composite natural isomorphism $\theta\circ\eta:F\cong H$ is unitary.

*Proof sketch.* (1) The condition reads $\mathrm{id}^*\circ\xi_M\circ\mathrm{id}=\xi_M$. (2) Since $(\theta\eta)_M^*=\eta_M^*\theta_M^*$,
$$(\theta\eta)_M^*\,\omega_M\,(\theta\eta)_{M^*}=\eta_M^*\bigl(\theta_M^*\,\omega_M\,\theta_{M^*}\bigr)\eta_{M^*}=\eta_M^*\,\zeta_M\,\eta_{M^*}=\xi_M,$$
using unitarity of $\theta$ and then of $\eta$.

## Sources

- [Ranicki 1992, §1](../../../../../sources/paper/ranicki-1992.md) [U]

## Depends on

- [Small Q-linear category with strict duality](../categories/duality-category.md)
- [Duality functor](../categories/duality-functor.md)
- [Unitary natural isomorphism](../categories/unitary-isomorphism.md)
