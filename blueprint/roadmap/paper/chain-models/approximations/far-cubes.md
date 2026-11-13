---
article_id: af_bb444c98557019546a8618f4
declaration: def
origin: bridged
statement: formalized
lean: HSP.ChainModels.IsFarCube
---

# Far cubes

A [grid cube](../grid/cubical/grid-cube.md) $c$ of $C(k)$ is *far* if its [closed cube](../grid/cubical/grid-cube-realization.md) $|c|\subseteq\mathbb T^n$ misses $\overline B(0,3/2)$, the image of the closed Euclidean ball of radius $3/2$ under the [quotient map](../torus/proj.md).

**Remark (not formalized).** A face of a far cube is far, since its closed cube is contained in that of the cube; so the far cubes span a subcomplex $E(k)\subseteq C(k)$.

## Sources

- New: replaces simplicial approximation (HS paper, Section 9).

## Depends on

- [Grid cubes](../grid/cubical/grid-cube.md)

## Proof depends on

- [The closed cube](../grid/cubical/grid-cube-realization.md)
- [The torus](../grid/torus.md)
- [The quotient map](../torus/proj.md)
