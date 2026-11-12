---
article_id: af_11953049a7e78ba4884bcd2f
declaration: abbrev
origin: bridged
statement: formalized
lean: HSP.Compression.discardProj
---
# Projection onto the discarded cells

Take [fixed local data](../local-data/control/fixed-local-data.md) with [start index](start-index.md) $i_0$, and let $D_i$ be the [chain model](../chain-models/grid/model/chain-model.md) at level $i$, a complex of [based vector spaces](../l-theory/localization/products/bookkeeping/based-category.md), with [retained projection](retained-projection.md) $\mathrm{pr}_i:D_i\to C_i$ and [retained inclusion](retained-inclusion.md) $\mathrm{in}_i:C_i\to D_i$. The endomorphism
$$Q_i=1-\mathrm{in}_i\,\mathrm{pr}_i:D_i\to D_i$$
is taken in each degree $r$, as a square matrix on the basis of $(D_i)_r$. For $i\ge i_0$ it is the based projection onto the span of the discarded cells, the cells that are not [retained](retained-cells.md): it fixes the basis vector of a discarded cell and sends that of a retained cell to $0$. For $i<i_0$, where $\mathrm{in}_i=0$ and $\mathrm{pr}_i=0$, $Q_i=1$. On cochains the corresponding map is the transpose $Q_i^*$.

## Sources
- HS paper, Section 10 (the quotient by far simplices).

## Depends on

- [Fixed local data](../local-data/control/fixed-local-data.md)
- [Chain model](../chain-models/grid/model/chain-model.md)
- [The category of based ℚ-vector spaces](../l-theory/localization/products/bookkeeping/based-category.md)

## Proof depends on

- [Retained projection](retained-projection.md)
- [Retained inclusion](retained-inclusion.md)
