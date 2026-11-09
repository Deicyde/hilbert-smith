---
article_id: af_ca496cdd8d39cea161e9a537
declaration: lemma
origin: background
---

# Duality functors carry pairs to pairs

Let $(F,\xi):\mathcal A\to\mathcal B$ be a duality functor, and write $F$ also for its [completion](../../base/categories/karoubi-functor.md). If $(f:C\to D,\delta\phi,\phi)$ is a strict $n$-dimensional Poincaré pair in $\mathrm{Kar}\,\mathcal A$, then $(Ff:FC\to FD,\ F_\%\delta\phi,\ F_\%\phi)$ is a strict $n$-dimensional Poincaré pair in $\mathrm{Kar}\,\mathcal B$, where $(F_\%\phi)_r=F(\phi_r)\circ\xi^{-1}_{C_{n-1-r}}$ and likewise for $\delta\phi$.

*Proof sketch.* (1) Naturality of $\xi$ gives $\xi\circ F(d^*)=(Fd)^*\circ\xi$, so $F_\%$ commutes with $\partial$. With $\xi_M^*=\xi_{M^*}$ it also commutes with $T$. Hence $F_\%\phi$ and $F_\%\delta\phi$ are $T$-invariant, $\partial F_\%\phi=0$, and $\partial F_\%\delta\phi=F_\%(f_\%\phi)=(Ff)_\%F_\%\phi$. (2) $F$ sends zero objects to zero objects, so the bounds on $FC$ and $FD$ hold. (3) $(F_\%\phi)_\natural=F(\phi_\natural)\circ\xi^{-1}$, where $\xi:F(C^{n-1-*})\to(FC)^{n-1-*}$ is an isomorphism of complexes. Since $F$ preserves chain homotopies, $(FC,F_\%\phi)$ is Poincaré. (4) Let $\kappa:F(\mathcal C(f))\to\mathcal C(Ff)$ be the canonical isomorphism, $F$ being additive. The [pair map](../../base/pairs/pair-map.md) of the image is $\kappa\circ F(\psi)\circ\xi^{-1}$, so it is a chain homotopy equivalence.

## Sources

- New: direct from the definitions

## Depends on

- [Strict Poincaré pair](../../base/pairs/poincare-pair.md)
- [Completion of a duality functor](../../base/categories/karoubi-functor.md)

## Proof depends on

- [Pair map](../../base/pairs/pair-map.md)
- [Mapping cone](../../base/complexes/cone.md)
