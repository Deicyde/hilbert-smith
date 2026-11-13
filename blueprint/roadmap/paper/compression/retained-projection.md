---
article_id: af_dc5f4bf8861603f872634fb9
declaration: def
origin: bridged
statement: formalized
lean: HSP.Compression.retainedProj
---
# Retained projection

Take [fixed local data](../local-data/control/fixed-local-data.md) with [start index](start-index.md) $i_0$, let $D_i$ be the [chain model](../chain-models/grid/model/chain-model.md) at level $i$, a complex of [based vector spaces](../l-theory/localization/products/bookkeeping/based-category.md), and let $C$ be the [compressed complex](compressed-complex.md), whose degree-$r$ part is an object of the [asymptotic category](../categories/asymptotic/asymptotic-category.md) with basis at level $i$ the [retained cells](retained-cells.md) of $(D_i)_r$ in increasing order. For $i\ge i_0$, the *retained projection* $\mathrm{pr}_i:D_i\to C_i$ is the based projection onto the span of the retained cells: in each degree $r$ it is the matrix from the basis of $(D_i)_r$ to that of $(C_i)_r$ that sends the basis vector of a retained cell to the same basis vector of $C_i$, and every other cell to $0$. For $i<i_0$, where $C_i=0$, $\mathrm{pr}_i=0$. On cochains the corresponding map is the transpose $\mathrm{pr}_i^*$.

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

- [Start index](start-index.md)
