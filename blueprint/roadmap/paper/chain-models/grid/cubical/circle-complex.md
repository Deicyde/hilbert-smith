---
article_id: af_63915f71e2a2de7a0189d865
declaration: def
origin: background
statement: formalized
lean: HSP.ChainModels.circleComplex
---

# The circle complex

For $k\in\mathbb N$, the *circle complex* $S_k$ is the complex of [based vector spaces](../../../l-theory/localization/products/based-vector-spaces.md) with basis $[w]$ of $S_{k,0}$ and $e_w$ of $S_{k,1}$, both indexed by $w\in\mathbb Z/k=\{0,\dots,k-1\}$ and enumerated in this order, zero in other degrees, and differential $de_w=[w+1]-[w]$. The realization of $[w]$ is the point $4w/k$ of $\mathbb R/4\mathbb Z$, and the realization of $e_w$ is the arc from $4w/k$ to $4(w+1)/k$.

## Sources

- New: companion of the cubical torus grid.

## Depends on

- [Based vector spaces](../../../l-theory/localization/products/based-vector-spaces.md)
- [The torus](../torus.md)
