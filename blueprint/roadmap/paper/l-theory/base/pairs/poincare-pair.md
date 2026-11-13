---
article_id: af_211ee442030db90eba876f31
declaration: structure
origin: bridged
statement: formalized
lean: HSP.SymPair
---

# Strict Poincaré pair

A *strict $n$-dimensional symmetric Poincaré pair* in a duality category $\mathcal B$ is $(f:C\to D,\delta\phi,\phi)$. Here, with $m=n-1$, $(C,\phi)$ is a strict $m$-dimensional symmetric Poincaré complex, $D_r$ is a zero object for every $r$ outside $[0,n]$, $\delta\phi\in M(D)_n$, $T\delta\phi=\delta\phi$, $\partial\delta\phi=f_\%\phi$, and the [pair map](pair-map.md) $\psi:D^{n-*}\to\mathcal C(f)$ is a chain homotopy equivalence. Its *boundary* is $(C,\phi)$. Its *chain objects* are the objects $C_r$ and $D_r$.

## Sources

- [Ranicki 1980 I, §3](../../../../../sources/paper/ranicki-1980.md) [U]

## Depends on

- [Pair map](pair-map.md)
- [Small Q-linear category with strict duality](../categories/duality-category.md)
- [A duality category has binary direct sums](../categories/sums/dual-binary-biproducts.md)
- [Mapping cone](../complexes/cone.md)
- [Duality map of a cycle](../complexes/cycle-chain-map.md)
- [Dual complex](../complexes/dual-complex.md)
- [Structure complex](../complexes/structure-complex.md)
- [The involution T](../complexes/structure-involution.md)
- [Pushforward of structures](../complexes/structure-push.md)

## Proof depends on

- [Strict symmetric Poincaré complex](symmetric-poincare-complex.md)
