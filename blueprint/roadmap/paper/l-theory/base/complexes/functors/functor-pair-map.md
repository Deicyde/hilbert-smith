---
article_id: af_c8ceb3371456e40b76807237
declaration: lemma
origin: background
statement: formalized
lean: HSP.DualFunctor.pairMap_map
proof: formalized
---

# Duality functors and pair maps

Let $(F,\xi):\mathcal B\to\mathcal B'$ be a [duality functor](../../categories/duality-functor.md), $f:C\to D$ a chain map, $\phi\in M(C)_m$ a cycle and $\delta\phi\in M(D)_n$ with $n=m+1$ and $\partial\delta\phi=f_\%\phi$, so that the [pair map](../../pairs/pair-map.md) $\psi:D^{n-*}\to\mathcal C(f)$ is defined. Then the [images](functor-structure.md) satisfy the same conditions for $Ff$, and the pair map $\psi^F$ of $(Ff,F_\%\delta\phi,F_\%\phi)$ is
$$\psi^F=\kappa\circ F(\psi)\circ\xi^{-1}:(FD)^{n-*}\to F(D^{n-*})\to F(\mathcal C(f))\to\mathcal C(Ff),$$
with $\xi^{-1}$ the isomorphism of [Duality functors and dual complexes](functor-dual-iso.md) and $\kappa$ that of [Duality functors and mapping cones](functor-cone.md).

*Proof sketch.* In degree $r$, both sides have $D$-component $F(\delta\phi_r)\circ\xi^{-1}$ and $C$-component $(-1)^rF(\phi_{r-1})\circ F(f^*)\circ\xi^{-1}=(-1)^rF(\phi_{r-1})\circ\xi^{-1}\circ(Ff)^*$, by naturality of $\xi$.

## Sources

- New: direct from the definitions.

## Depends on

- [Duality functor](../../categories/duality-functor.md)
- [Pair map](../../pairs/pair-map.md)
- [Image of structures under a duality functor](functor-structure.md)
- [Duality functors and dual complexes](functor-dual-iso.md)
- [Duality functors and mapping cones](functor-cone.md)
