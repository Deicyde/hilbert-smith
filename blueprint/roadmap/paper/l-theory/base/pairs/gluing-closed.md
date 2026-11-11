---
article_id: af_c1b3c6f08425e313bd80bd97
declaration: lemma
origin: bridged
---

# Closed gluing

If $C_{B,r}$ is a zero object for every $r$, then $(U,\Phi)$ is a strict $n$-dimensional symmetric Poincaré complex.

*Proof sketch.* (1) [Gluing](gluing.md) makes $(g_B:C_B\to U,\Phi,\phi_B)$ a strict $n$-dimensional Poincaré pair, so $T\Phi=\Phi$, $U_r$ is a zero object for $r$ outside $[0,n]$, and the [pair map](pair-map.md) $\Psi:U^{n-*}\to\mathcal C(g_B)$ is a chain homotopy equivalence. (2) Every map into or out of a zero object is zero, so $g_B=0$ and $\partial\Phi=g_{B\%}\phi_B=0$. (3) The projection $\pi:\mathcal C(g_B)\to U$, $(x,y)\mapsto x$, is a chain map because $g_B=0$, and an isomorphism of complexes with inverse $x\mapsto(x,0)$, since each $C_{B,r-1}$ is a zero object. (4) $\pi\Psi=\Phi_\natural$, the first component of the pair map. So $\Phi_\natural$ is a chain homotopy equivalence.

## Sources

- [Ranicki 1980 I, §3](../../../../../sources/paper/ranicki-1980.md) [U]

## Depends on

- [Algebraic union](algebraic-union.md)

## Proof depends on

- [Gluing](gluing.md)
- [Pair map](pair-map.md)
- [Mapping cone](../complexes/cone.md)
- [Duality map of a cycle](../complexes/cycle-chain-map.md)
