---
article_id: af_d08fca90ca86740ad150a707
declaration: def
origin: bridged
statement: formalized
lean: HSP.pairMap
---

# Pair map

Let $f:C\to D$ be a chain map, $m=n-1$, $\phi\in M(C)_m$ with $\partial\phi=0$, and $\delta\phi\in M(D)_n$ with $\partial\delta\phi=f_\%\phi$. Then $\psi_r=(\delta\phi_r,\ (-1)^r\phi_{r-1}f^*_{n-r}):D^*_{n-r}\to\mathcal C(f)_r$ is a chain map $\psi:D^{n-*}\to\mathcal C(f)$.

## Sources

- [Ranicki 1980 I, §3](../../../../../sources/paper/ranicki-1980.md) [U]
- New: the sign is the one that makes $\psi$ a chain map

## Depends on

- [Mapping cone](../complexes/cone.md)
- [Pushforward of structures](../complexes/structure-push.md)
- [A duality category has binary direct sums](../categories/sums/dual-binary-biproducts.md)
- [Small Q-linear category with strict duality](../categories/duality-category.md)
- [Dual complex](../complexes/dual-complex.md)
- [Structure complex](../complexes/structure-complex.md)
