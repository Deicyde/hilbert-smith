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
- [Small Q-linear category with strict duality](../categories/duality-category.md)

## Proof depends on

- [Duality functors carry Poincaré complexes](functor-poincare.md)
- [Duality functors commute with pushforward](../complexes/functor-push.md)
- [Pair map](pair-map.md)
- [Mapping cone](../complexes/cone.md)
- [Pushforward of structures](../complexes/structure-push.md)
- [Images of structures commute with the boundary, T and the duality map](../complexes/functors/functor-structure-laws.md)
- [Duality functors and dual complexes](../complexes/functors/functor-dual-iso.md)
- [Duality functors and mapping cones](../complexes/functors/functor-cone.md)
- [Duality functors and pair maps](../complexes/functors/functor-pair-map.md)
- [A duality category has binary direct sums](../categories/sums/dual-binary-biproducts.md)
- [Duality map of a cycle](../complexes/cycle-chain-map.md)
- [Dual complex](../complexes/dual-complex.md)
- [Image of a complex under a duality functor](../complexes/functors/functor-complex.md)
- [Image of structures under a duality functor](../complexes/functors/functor-structure.md)
- [Structure complex](../complexes/structure-complex.md)
- [The involution T](../complexes/structure-involution.md)
- [Strict symmetric Poincaré complex](symmetric-poincare-complex.md)
