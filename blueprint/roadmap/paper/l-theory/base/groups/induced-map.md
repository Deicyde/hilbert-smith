---
article_id: af_f43570e8796a48f1d3a478bd
declaration: def
origin: bridged
statement: formalized
lean: HSP.LGroup.map
---

# Induced homomorphism

A duality functor $(F,\xi):\mathcal B\to\mathcal B'$ induces a homomorphism $F_*:L_k(\mathcal B)\to L_k(\mathcal B')$, $[C,\phi]\mapsto[FC,F_\%\phi]$, with $(F_\%\phi)_r=F(\phi_r)\circ\xi^{-1}_{C_{k-r}}$. On projective L-groups, a duality functor $F:\mathcal A\to\mathcal A'$ acts by $F_*:=(\mathrm{Kar}\,F)_*:L^p_k(\mathcal A)\to L^p_k(\mathcal A')$, with $\mathrm{Kar}\,F$ the [completion](../categories/karoubi-functor.md) of $F$.

*Proof sketch.* (1) $(FC,F_\%\phi)$ is a strict $k$-dimensional symmetric Poincaré complex by [Duality functors carry Poincaré complexes](../pairs/functor-poincare.md). (2) $F$ carries cobordant complexes to cobordant complexes, and the image of $(C,\phi)\oplus(C',\phi')$ is cobordant to $(FC,F_\%\phi)\oplus(FC',F_\%\phi')$, by [Duality functors on cobordism classes](induced-map-laws.md); so $F_*$ is well defined and additive.

## Sources

- New: direct from the definitions

## Depends on

- [Group structure on L](l-group-add.md)
- [Duality functor](../categories/duality-functor.md)
- [Completion of a duality functor](../categories/karoubi-functor.md)

## Proof depends on

- [Duality functors carry Poincaré complexes](../pairs/functor-poincare.md)
- [Duality functors on cobordism classes](induced-map-laws.md)
