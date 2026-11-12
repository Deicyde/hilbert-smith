---
article_id: af_29880dbdc85f69b5d928091f
declaration: def
origin: background
statement: formalized
lean: HSP.ChainModels.cubeSpan
---
# Spans of cubes

Let $S$ be a set of [grid cubes](cubical/grid-cube.md) of $\mathbb T^n$ for the grid $\mathbb Z/k$, and $r\in\mathbb Z$. The *span* of $S$ in degree $r$ is the subspace of $C(k)_r=\mathbb Q^{N_r}$, the degree-$r$ part of the [cubical torus grid](cubical/cubical-torus-grid.md), of the vectors whose coordinate vanishes at every basis vector whose [cube](cubical/grid-cell.md) is not in $S$. It is spanned by the basis vectors whose cubes lie in $S$.

## Sources
- New.

## Depends on
- [Grid cubes](cubical/grid-cube.md)
- [Cubical torus grid](cubical/cubical-torus-grid.md)
- [The cube of a basis vector](cubical/grid-cell.md)
