---
article_id: af_078a65cf2fae004f3c008dda
declaration: lemma
origin: background
statement: formalized
lean: HSP.Compression.pr_d_Q
---
# The discarded cells form a subcomplex

Let $\mathrm{pr}_i$ be the based projection of $D_i$ onto the span of the [retained cells](retained-cells.md) and $Q_i$ the based projection onto the span of the discarded cells. Then $\mathrm{pr}_i\,d\,Q_i=0$ and $Q_i^*\,d^*\,\mathrm{pr}_i^*=0$.

*Proof sketch.* The cells occurring in $d(c\otimes e_r)$ are $c'\otimes e_r$ with $c'$ a face of $c$, because $P$ has zero differential. Then $|c'|\subseteq|c|$, so $c'$ misses $K_t$ whenever $c$ does: the entry of $d$ from a discarded cell to a retained cell is zero. The second identity is the transpose of the first.

## Sources
- HS paper, Section 10.

## Depends on

- [Retained cells](retained-cells.md)
- [Retained projection](retained-projection.md)
- [Chain model](../chain-models/grid/chain-model.md)

## Proof depends on

- [Cells of CP^2](../chain-models/grid/cp2-cells.md)
