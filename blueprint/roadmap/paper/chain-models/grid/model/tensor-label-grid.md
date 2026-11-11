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
2. Label the basis of the [grid complex](../cubical/cubical-torus-grid.md) $C(k)$ by the [centers](../cubical/grid-cube-center.md) of the [cubes of its basis vectors](../cubical/grid-cell.md), and the cells of $S_k$ by their centers as in [circle duality](../circle-duality.md). Then the labels of $C(k)\otimes S_k$ are the [tensor labels](tensor-label.md) of those of $C(k)$ and $S_k$, combined by appending a coordinate.
3. The [torus labels](chain-model-label.md) of the [chain model](chain-model.md) $D_i=C(k_i)\otimes P$ are the tensor labels of the center labels of $C(k_i)$ and any labels of $P$, combined by forgetting the second factor.

*Proof sketch.* (1) holds coordinatewise for the sup metric. (2) and (3) hold by definition: the cube of $x\otimes y$ is the cube of $x$ followed by the cell of $y$, and the cube of a chain-model cell $c\otimes e$ is the cube of $c$.

## Sources

- New: the explicit chain model of the cubical grid.

## Depends on

- [Labels on a tensor product of based complexes](tensor-label.md)
- [Cubical torus grid](../cubical/cubical-torus-grid.md)
- [The cube of a basis vector](../cubical/grid-cell.md)
- [The center of a grid cube](../cubical/grid-cube-center.md)
- [Circle duality](../circle-duality.md)
- [Torus labels of chain-model cells](chain-model-label.md)
- [Chain model](chain-model.md)
