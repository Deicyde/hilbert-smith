---
article_id: af_a22e26654a07d33ff45e11aa
declaration: def
origin: bridged
statement: formalized
lean: HSP.ChainModels.gridDualMap
---

# The iterated grid duality map

For $k\ge1$, the iterated duality map $b^{(n)}:C(k)\to C(k)^{n-*}$ of the [grid complex](../../cubical/cubical-torus-grid.md) is given by its components: $b^{(0)}$ is the identity of $\mathbb Q$ in degree $0$ on the [unit complex](../../cubical/unit-complex.md), and $b^{(n+1)}$ is the [product of duality maps](../../tensor/structure-products/based-dual-prod.md) of $b^{(n)}$ with the [circle inverse](../circle-data/circle-b.md) $b$. So $b^{(n)}=\Xi^{-1}\circ(b\otimes\cdots\otimes b)$.

## Sources

- New: the explicit chain model of the cubical grid.

## Depends on

- [Cubical torus grid](../../cubical/cubical-torus-grid.md)
- [The unit complex](../../cubical/unit-complex.md)
- [Product of duality maps in explicit bases](../../tensor/structure-products/based-dual-prod.md)
- [The circle inverse](../circle-data/circle-b.md)
