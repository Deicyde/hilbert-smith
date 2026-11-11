---
article_id: af_f8ef6e550e360aa57d7883b4
declaration: lemma
origin: background
---

# Closed complexes are pairs with zero boundary

Let $Z$ be a complex in $\mathrm{Kar}\,\mathcal A$ whose chain objects are zero objects, let $C$ be a complex whose chain objects are zero objects outside $[0,n]$, and let $\phi\in M(C)_n$ with $\partial\phi=0$ and $T\phi=\phi$. Then $(0:Z\to C,\ \phi,\ 0)$ is a strict $n$-dimensional Poincaré pair iff $(C,\phi)$ is a strict $n$-dimensional symmetric Poincaré complex.

*Proof sketch.* (1) $(Z,0)$ is a strict $(n-1)$-dimensional Poincaré complex: $0_\natural$ is a map between complexes of zero objects, hence an isomorphism. (2) $\partial\phi=0=0_\%0$. (3) In $\mathcal C(0)_r=C_r\oplus Z_{r-1}$ the second summand is a zero object, so the projection $\mathcal C(0)\to C$ is an isomorphism of complexes. Composed with the [pair map](../../base/pairs/pair-map.md) $\psi_r=(\phi_r,0)$ it gives $\phi_\natural$. So $\psi$ is a chain homotopy equivalence iff $\phi_\natural$ is.

## Sources

- New: direct from the definitions

## Depends on

- [Strict Poincaré pair](../../base/pairs/poincare-pair.md)
- [Strict symmetric Poincaré complex](../../base/pairs/symmetric-poincare-complex.md)

## Proof depends on

- [Pair map](../../base/pairs/pair-map.md)
- [Mapping cone](../../base/complexes/cone.md)
