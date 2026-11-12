---
article_id: af_c258acede56fc836a29d0243
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.ChainModels.tensorLabel_grid
---

# Grid and chain-model labels are tensor labels

1. Appending a coordinate, $\mathbb T^n\times(\mathbb R/4\mathbb Z)\to\mathbb T^{n+1}$, is $1$-Lipschitz for the max distance.
2. Label the basis of the grid complex $C(k)$ by the [centers](../cubical/grid-cube-center.md) of the [cubes of its basis vectors](../cubical/grid-cell.md), and the cells of $S_k$ by [their centers](../cubical/circle-label.md). Then the labels of $C(k)\otimes S_k$ are the [tensor labels](tensor-label.md) of those of $C(k)$ and $S_k$, combined by appending a coordinate.
3. The [torus labels](chain-model-label.md) of the chain model $D_i=C(k_i)\otimes P$ are the tensor labels of the center labels of $C(k_i)$ and the constant label $0\in\mathbb R$ on every cell of $P$, combined by forgetting the second factor.

*Proof sketch.* (1) holds coordinatewise for the sup metric. (2) and (3) hold by definition: the cube of $x\otimes y$ is the cube of $x$ followed by the cell of $y$, and the cube of a chain-model cell $c\otimes e$ is the cube of $c$.

## Sources

- New: the explicit chain model of the cubical grid.

## Depends on

- [Labels of the circle cells](../cubical/circle-label.md)
- [Labels on a tensor product of based complexes](tensor-label.md)
- [The cube of a basis vector](../cubical/grid-cell.md)
- [The center of a grid cube](../cubical/grid-cube-center.md)
- [Torus labels of chain-model cells](chain-model-label.md)
- [The cells of CP^2 vanish in negative degrees](../cp2/cp2-dim-neg.md)
- [The circle complex vanishes in negative degrees](../cubical/circle-dim-neg.md)
- [Mesh sequence](../mesh-sequence.md)
- [The torus](../torus.md)
- [Local datum](../../../local-data/chart/local-datum.md)
