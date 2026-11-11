---
article_id: af_2ad500238b676a2e659bde77
declaration: def
origin: background
statement: formalized
lean: HSP.SymPoincare.map
---

# Duality functors carry Poincaré complexes

Let $(F,\xi):\mathcal B\to\mathcal B'$ be a [duality functor](../categories/duality-functor.md) and $(C,\phi)$ a [strict $k$-dimensional symmetric Poincaré complex](symmetric-poincare-complex.md) in $\mathcal B$. Its *image under $F$* is the strict $k$-dimensional symmetric Poincaré complex $(FC,F_\%\phi)$ in $\mathcal B'$, with $(F_\%\phi)_r=F(\phi_r)\circ\xi^{-1}_{C_{k-r}}$. If $F$ is strict, then $F_\%\phi=F\phi$.

*Proof sketch.* (Proof obligations.) (1) Naturality of $\xi$ gives $\xi\circ F(d^*)=(Fd)^*\circ\xi$, so $F_\%$ commutes with $\partial$; with $\xi_M^*=\xi_{M^*}$ it also commutes with [the involution $T$](../complexes/structure-involution.md). Hence $F_\%\phi$ is a $T$-invariant cycle. (2) $F$ sends zero objects to zero objects, so $FC$ satisfies the bounds. (3) $(F_\%\phi)_\natural=F(\phi_\natural)\circ\xi^{-1}$, where $\xi:F(C^{k-*})\to(FC)^{k-*}$, given by $\xi_{C_{k-r}}$ in degree $r$, is an isomorphism of complexes by naturality of $\xi$ and the definition of the [dual complex](../complexes/dual-complex.md), and $F$ preserves chain homotopies, so $(F_\%\phi)_\natural$ is a chain homotopy equivalence. For strict $F$, $\xi$ is the identity.

## Sources

- New: direct from the definitions.

## Depends on

- [Duality functor](../categories/duality-functor.md)
- [Strict symmetric Poincaré complex](symmetric-poincare-complex.md)

## Proof depends on

- [Structure complex](../complexes/structure-complex.md)
- [Duality map of a cycle](../complexes/cycle-chain-map.md)
- [The involution T](../complexes/structure-involution.md)
- [Dual complex](../complexes/dual-complex.md)
