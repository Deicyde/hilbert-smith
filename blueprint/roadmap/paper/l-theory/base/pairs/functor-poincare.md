---
article_id: af_2ad500238b676a2e659bde77
declaration: def
origin: background
statement: formalized
lean: HSP.SymPoincare.map, HSP.DualFunctor.mapStructure_apply_of_isStrict
---

# Duality functors carry Poincaré complexes

Let $(F,\xi):\mathcal B\to\mathcal B'$ be a [duality functor](../categories/duality-functor.md) and $(C,\phi)$ a [strict $k$-dimensional symmetric Poincaré complex](symmetric-poincare-complex.md) in $\mathcal B$. Its *image under $F$* is the strict $k$-dimensional symmetric Poincaré complex $(FC,F_\%\phi)$ in $\mathcal B'$, formed from the [image of the complex](../complexes/functors/functor-complex.md) and the [image of the structure](../complexes/functors/functor-structure.md), with $(F_\%\phi)_r=F(\phi_r)\circ\xi^{-1}_{C_{k-r}}$. If $F$ is [strict](../categories/duality-functors/strict-duality-functor.md), then for every element $f$ of the [structure complex](../complexes/structure-complex.md) $M(C)_n$ of a complex $C$ in $\mathcal B$ and every $r+s=n$, $(F_\%f)_{r,s}=F(f_{r,s})$, reading $(FC_s)^*=F(C_s^*)$; in particular $(F_\%\phi)_r=F(\phi_r)$, reading $(FC_{k-r})^*=F(C_{k-r}^*)$.

*Proof sketch.* (Proof obligations.) (1) $F_\%$ commutes with $\partial$ and with [the involution $T$](../complexes/structure-involution.md) ([Images of structures commute with the boundary, T and the duality map](../complexes/functors/functor-structure-laws.md)), so $F_\%\phi$ is a $T$-invariant cycle. (2) $F$ sends zero objects to zero objects, so $FC$ satisfies the bounds. (3) $(F_\%\phi)_\natural=F(\phi_\natural)\circ\xi^{-1}$ by the same lemma, where $\xi^{-1}:(FC)^{k-*}\cong F(C^{k-*})$ is the isomorphism of [Duality functors and dual complexes](../complexes/functors/functor-dual-iso.md), and $F$ preserves chain homotopies, so $(F_\%\phi)_\natural$ is a chain homotopy equivalence. For strict $F$, $\xi$ is the identity.

## Sources

- New: direct from the definitions.

## Depends on

- [Duality functor](../categories/duality-functor.md)
- [Strict symmetric Poincaré complex](symmetric-poincare-complex.md)
- [Image of a complex under a duality functor](../complexes/functors/functor-complex.md)
- [Image of structures under a duality functor](../complexes/functors/functor-structure.md)
- [Structure complex](../complexes/structure-complex.md)
- [Strict duality functor](../categories/duality-functors/strict-duality-functor.md)

## Proof depends on

- [Duality map of a cycle](../complexes/cycle-chain-map.md)
- [The involution T](../complexes/structure-involution.md)
- [Dual complex](../complexes/dual-complex.md)
- [Images of structures commute with the boundary, T and the duality map](../complexes/functors/functor-structure-laws.md)
- [Duality functors and dual complexes](../complexes/functors/functor-dual-iso.md)
