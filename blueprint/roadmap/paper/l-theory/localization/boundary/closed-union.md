---
article_id: af_ebc30d0d0750be121451be15
declaration: def
origin: bridged
---

# Closing a pair by a null-cobordism of its boundary

Let $V=(f:iP\to D,\delta\phi,i_\%\pi)$ be a strict $k$-dimensional [$\mathcal U$-pair](u-pair.md), and let $R=(g:P\to R_\bullet,\rho,-\pi)$ be a strict $k$-dimensional Poincaré pair in $\mathrm{Kar}\,\mathcal U$ with boundary $(P,-\pi)$. Let $Z$ be the zero complex and $u:Z\oplus iP\to iP$ the canonical isomorphism, and let $R'=(ig\circ u,\ i_\%\rho,\ 0\oplus(-i_\%\pi))$. The *closed union* is the [algebraic union](../../base/pairs/algebraic-union.md)
$$D\cup_PR:=V\cup_{iP}R',$$
a strict $k$-dimensional symmetric Poincaré complex $(D\cup_PR,\Phi)$ in $\mathrm{Kar}\,\mathcal A$ with chain objects $D_r\oplus iR_{\bullet,r}\oplus iP_{r-1}$.

*Proof sketch.* (The union is defined and Poincaré.) (1) $(ig,i_\%\rho,-i_\%\pi)$ is a strict pair in $\mathrm{Kar}\,\mathcal A$ by [Duality functors carry pairs to pairs](functor-pair.md), $i$ being strict. (2) $u$ is an isomorphism carrying $0\oplus(-i_\%\pi)$ to $-i_\%\pi$, so $R'$ is a strict pair with boundary $(Z\oplus iP,0\oplus(-i_\%\pi))$ by [Pair transport](../../base/pairs/pair-transport.md). This is the shape of $V_B$ in the algebraic union with $C_B=Z$. (3) [Closed gluing](../../base/pairs/gluing-closed.md).

## Sources

- [Ranicki 1980 I, §3, union of pairs](../../../../../sources/paper/ranicki-1980.md) [U]
- New: the transport that puts $R$ in the one-sided form of the algebraic union

## Depends on

- [U-pairs](u-pair.md)
- [Algebraic union](../../base/pairs/algebraic-union.md)
- [Strict Poincaré pair](../../base/pairs/poincare-pair.md)

## Proof depends on

- [Duality functors carry pairs to pairs](functor-pair.md)
- [Pair transport](../../base/pairs/pair-transport.md)
- [Closed gluing](../../base/pairs/gluing-closed.md)
