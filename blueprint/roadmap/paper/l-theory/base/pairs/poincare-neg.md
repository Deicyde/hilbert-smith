---
article_id: af_740fd83d1d3bd777a90c717a
declaration: def
origin: background
statement: formalized
lean: HSP.SymPoincare.neg
---

# Negative of a Poincaré complex

For a strict $k$-dimensional symmetric Poincaré complex $(C,\phi)$ in a duality category $\mathcal B$, its *negative* $(C,-\phi)$ is a strict $k$-dimensional symmetric Poincaré complex.

*Proof sketch.* (Proof obligations.) $-\phi$ is a $T$-invariant cycle, since $\partial$ and $T$ are linear. $(-\phi)_\natural=-\phi_\natural$, and negating an equivalence, its inverse and its homotopies gives an equivalence.

## Sources

- [Ranicki 1980 I, §3](../../../../../sources/paper/ranicki-1980.md) [U]

## Depends on

- [Strict symmetric Poincaré complex](symmetric-poincare-complex.md)
- [Small Q-linear category with strict duality](../categories/duality-category.md)

## Proof depends on

- [Duality map of a cycle](../complexes/cycle-chain-map.md)
- [Dual complex](../complexes/dual-complex.md)
- [Structure complex](../complexes/structure-complex.md)
- [The involution T](../complexes/structure-involution.md)
