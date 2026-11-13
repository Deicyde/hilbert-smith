---
article_id: af_1618bd3948b7fa2aa1dff71b
declaration: abbrev
origin: bridged
statement: formalized
lean: HSP.Compression.retainedInc
---
# Retained inclusion

Take [fixed local data](../local-data/control/fixed-local-data.md) with [start index](start-index.md) $i_0$, let $D_i$ be the [chain model](../chain-models/grid/model/chain-model.md) at level $i$, a complex of [based vector spaces](../l-theory/localization/products/bookkeeping/based-category.md), let $C$ be the [compressed complex](compressed-complex.md), whose degree-$r$ part is an object of the [asymptotic category](../categories/asymptotic/asymptotic-category.md) of rank $\dim(C_i)_r$ at level $i$, and let $\mathrm{pr}_i:D_i\to C_i$ be the [retained projection](retained-projection.md). The *retained inclusion* $\mathrm{in}_i:C_i\to D_i$ is, in each degree $r$, the matrix from the basis of $(C_i)_r$ to the basis of $(D_i)_r$ that is the transpose of $\mathrm{pr}_i$. For $i\ge i_0$ it is the based inclusion of the span of the [retained cells](retained-cells.md): it sends the basis vector of a retained cell of $C_i$ to the same basis vector of $D_i$. For $i<i_0$, where $C_i=0$, $\mathrm{in}_i=0$. On cochains $\mathrm{pr}_i^*=\mathrm{in}_i$ and $\mathrm{in}_i^*=\mathrm{pr}_i$ in the dual degrees.

## Sources
- HS paper, Section 10 (the quotient by far simplices).

## Depends on

- [Fixed local data](../local-data/control/fixed-local-data.md)
- [Chain model](../chain-models/grid/model/chain-model.md)
- [The category of based ℚ-vector spaces](../l-theory/localization/products/bookkeeping/based-category.md)
- [Compressed complex](compressed-complex.md)
- [Asymptotic category](../categories/asymptotic/asymptotic-category.md)
- [The trivial group sequence](../categories/asymptotic/trivial-group-sequence.md)
- [The round sphere](../corner/round-sphere.md)
- [The cyclic action on the control space](../local-data/control/control-action.md)
- [The metric on the control space](../local-data/control/control-metric-space.md)
- [The control space](../local-data/control/control-space.md)

## Proof depends on

- [Retained projection](retained-projection.md)
