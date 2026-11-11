---
article_id: af_ca496cdd8d39cea161e9a537
declaration: def
origin: background
statement: formalized
lean: HSP.SymPair.map
---

# Duality functors carry pairs to pairs

Let $(F,\xi):\mathcal B\to\mathcal B'$ be a [duality functor](../categories/duality-functor.md) between duality categories and $(f:C\to D,\delta\phi,\phi)$ a strict $n$-dimensional Poincaré pair in $\mathcal B$. Its *image under $F$* is the strict $n$-dimensional Poincaré pair $(Ff:FC\to FD,\ F_\%\delta\phi,\ F_\%\phi)$ in $\mathcal B'$, where $(F_\%\phi)_r=F(\phi_r)\circ\xi^{-1}_{C_{n-1-r}}$ and likewise for $\delta\phi$. For a duality functor $\mathcal A\to\mathcal A'$ this is applied to its [completion](../categories/karoubi-functor.md) $\mathrm{Kar}\,\mathcal A\to\mathrm{Kar}\,\mathcal A'$.

*Proof sketch.* (Proof obligations.) (1)-(3) [Duality functors carry Poincaré complexes](functor-poincare.md), its steps (1) to (3) applied to $(C,\phi)$, makes $(FC,F_\%\phi)$ a strict $(n-1)$-dimensional Poincaré complex; the same steps for $D$ show that $F_\%\delta\phi$ is $T$-invariant, that $FD$ satisfies the bounds, and that $\partial F_\%\delta\phi=F_\%(f_\%\phi)=(Ff)_\%F_\%\phi$, because $F_\%$ commutes with $\partial$ and with pushforward along $f$. (4) Let $\kappa:F(\mathcal C(f))\to\mathcal C(Ff)$ be the canonical isomorphism, $F$ being additive. The [pair map](pair-map.md) of the image is $\kappa\circ F(\psi)\circ\xi^{-1}$, so it is a chain homotopy equivalence.

## Sources

- New: direct from the definitions

## Depends on

- [Duality functor](../categories/duality-functor.md)
- [Strict Poincaré pair](poincare-pair.md)
- [Completion of a duality functor](../categories/karoubi-functor.md)

## Proof depends on

- [Duality functors carry Poincaré complexes](functor-poincare.md)
- [Pair map](pair-map.md)
- [Mapping cone](../complexes/cone.md)
- [Images of structures commute with the boundary, T and the duality map](../complexes/functors/functor-structure-laws.md)
- [Duality functors and dual complexes](../complexes/functors/functor-dual-iso.md)
