---
article_id: af_078a65cf2fae004f3c008dda
declaration: lemma
origin: background
statement: formalized
proof: formalized
lean: HSP.Compression.pr_d_Q
---
# The discarded cells form a subcomplex

Take [fixed local data](../local-data/control/fixed-local-data.md) with [start index](start-index.md) $i_0$, and for every $i\in\mathbb N$ let $D_i$ be the [chain model](../chain-models/grid/model/chain-model.md), $\mathrm{pr}_i$ the [retained projection](retained-projection.md) and $Q_i=1-\mathrm{in}_i\,\mathrm{pr}_i$ the [projection onto the discarded cells](discard-projection.md). For $i\ge i_0$, $\mathrm{pr}_i$ is the based projection of $D_i$ onto the span of the [retained cells](retained-cells.md) and $Q_i$ the based projection onto the span of the discarded cells; for $i<i_0$, $\mathrm{pr}_i=0$ and $Q_i=1$. Then for every $i$ and every component $d:(D_i)_r\to(D_i)_s$ of the differential of $D_i$, $\mathrm{pr}_i\,d\,Q_i=0$ and $Q_i^*\,d^*\,\mathrm{pr}_i^*=0$.

*Proof sketch.* For $i<i_0$, the compressed rank at level $i$ is $0$ (no cell is kept below the start index), so $\mathrm{pr}_i\,d\,Q_i$ has no rows and vanishes. Let $i\ge i_0$. Label each basis cell by a set; call the labelling *monotone* if every nonzero entry of $d$ goes from a cell to a cell with smaller label. In the circle complex, labelling a cell by its closed arc is monotone, since $d$ takes the arc $[w]\times[0,1]$ to its two endpoints. The product labelling of a based tensor product of monotone labellings is monotone: the blocks of the tensor differential are Kronecker products of a differential with an identity, so a nonzero entry moves one factor down and keeps the other. Hence the cubical torus grid, built from the unit complex by tensoring with circle complexes, is monotone for the closed cubes of its cells, and so is $D_i=C(k_i)\otimes P$ for the label $|c|\times\{\mathrm{pt}\}$ of $c\otimes e$. So a nonzero entry of $d$ goes from a cell $c\otimes e$ to a cell $c'\otimes e'$ with $|c'|\subseteq|c|$, and $c'$ misses $K_t$ whenever $c$ does. Now $\mathrm{in}_i\,\mathrm{pr}_i$ is the diagonal projection onto the retained cells, so the entry of $\mathrm{pr}_i\,d\,Q_i$ at a retained cell $b$ and a cell $a$ is $d_{b,a}$ if $a$ is discarded and $0$ otherwise, and it vanishes by the above. The second identity is the transpose of the first.

## Sources
- HS paper, Section 10.

## Depends on

- [Fixed local data](../local-data/control/fixed-local-data.md)
- [Retained projection](retained-projection.md)
- [Projection onto the discarded cells](discard-projection.md)
- [Chain model](../chain-models/grid/model/chain-model.md)
- [Based category](../l-theory/localization/products/bookkeeping/based-category.md)
- [Asymptotic category](../categories/asymptotic/asymptotic-category.md)
- [The trivial group sequence](../categories/asymptotic/trivial-group-sequence.md)
- [Compressed complex](compressed-complex.md)
- [The round sphere](../corner/round-sphere.md)
- [The cyclic action on the control space](../local-data/control/control-action.md)
- [The metric on the control space](../local-data/control/control-metric-space.md)
- [The control space](../local-data/control/control-space.md)

## Proof depends on

- [Retained cells](retained-cells.md)
- [Retained inclusion](retained-inclusion.md)
- [Local datum](../local-data/chart/local-datum.md)
- [The torus](../chain-models/grid/torus.md)
- [Tensor product of based complexes](../chain-models/grid/based-complex-tensor.md)
- [Kronecker product of matrices](../l-theory/localization/products/bookkeeping/based-kron.md)
- [The circle complex](../chain-models/grid/cubical/circle-complex.md)
- [The circle complex vanishes in negative degrees](../chain-models/grid/cubical/circle-dim-neg.md)
- [The unit complex](../chain-models/grid/cubical/unit-complex.md)
- [Cubical torus grid](../chain-models/grid/cubical/cubical-torus-grid.md)
- [Grid cubes](../chain-models/grid/cubical/grid-cube.md)
- [The cube of a basis vector](../chain-models/grid/cubical/grid-cell.md)
- [Mesh sequence](../chain-models/grid/mesh-sequence.md)
- [The cellular chain complex of CP^2](../chain-models/grid/cp2/cp2-complex.md)
- [The cells of CP^2 vanish in negative degrees](../chain-models/grid/cp2/cp2-dim-neg.md)
- [The cube of a chain-model cell](../chain-models/grid/model/chain-model-cube.md)
- [Realization of a circle cell](../chain-models/grid/cubical/cell-realization.md)
- [The cell of a basis vector of the circle complex](../chain-models/grid/cubical/circle-cell.md)
- [Realization of a grid cube](../chain-models/grid/cubical/grid-cube-realization.md)
- [Start index](start-index.md)
- [Block inclusions and projections](../chain-models/grid/tensor/blocks/block-maps.md)
- [The preimage of the buffer ball](test-preimage.md)
