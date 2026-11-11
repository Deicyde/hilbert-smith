---
article_id: af_bb444c98557019546a8618f4
declaration: def
origin: bridged
statement: formalized
lean: HSP.ChainModels.IsFarCube
---

# Far cubes

A cube $c$ of the [cubical torus grid](../grid/cubical-torus-grid.md) $C(k)$ is *far* if its closed cube $|c|\subseteq\mathbb T^n$ misses $\overline B(0,3/2)$, the image of the closed Euclidean ball of radius $3/2$ under the [quotient map](../torus/proj.md). The far cubes span the subcomplex $E(k)\subseteq C(k)$: a face of a far cube is far.

## Sources

- New: replaces simplicial approximation (HS paper, Section 9).

## Depends on

- [The quotient map](../torus/proj.md), [cubical torus grid](../grid/cubical-torus-grid.md)
