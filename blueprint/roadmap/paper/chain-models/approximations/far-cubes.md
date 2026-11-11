---
article_id: af_bb444c98557019546a8618f4
declaration: def
origin: bridged
statement: formalized
lean: HSP.ChainModels.IsFarCube
---

# Far cubes

A cube $c$ of the [cubical torus grid](../grid/cubical/cubical-torus-grid.md) $C(k)$ is *far* if its closed cube $|c|\subseteq\mathbb T^n$ misses $\overline B(0,3/2)$, the image of the closed Euclidean ball of radius $3/2$ under the [quotient map](../torus/proj.md).

**Remark (not formalized).** A face of a far cube is far, since its closed cube is contained in that of the cube; so the far cubes span a subcomplex $E(k)\subseteq C(k)$.

## Sources

- New: replaces simplicial approximation (HS paper, Section 9).

## Depends on

- [The closed cube](../grid/cubical/grid-cube-realization.md)
- [Grid cubes](../grid/cubical/grid-cube.md)
- [The quotient map](../torus/proj.md), [cubical torus grid](../grid/cubical/cubical-torus-grid.md)
