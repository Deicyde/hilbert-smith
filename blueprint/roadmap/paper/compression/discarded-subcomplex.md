---
article_id: af_078a65cf2fae004f3c008dda
declaration: lemma
origin: background
---
# The discarded cells form a subcomplex

$dF_i\subseteq F_i$. Dually, $d^*$ maps the span of the duals of retained cells into itself. In matrix form, with $Q_i$ the projection onto $F_i$ and $\mathrm{pr}_i$ the projection onto the retained cells: $\mathrm{pr}_i\,d\,Q_i=0$ and $Q_i^*\,d^*\,\mathrm{pr}_i^*=0$.

*Proof sketch.* The cells occurring in $d(c\otimes e_r)$ are $c'\otimes e_r$ with $c'$ a face of $c$, because $P$ has zero differential. Then $|c'|\subseteq|c|$, so $c'$ misses $K_t$ whenever $c$ does. The second identity is the transpose of the first.

## Sources
- HS paper, Section 10.
## Depends on
- [Retained cells](retained-cells.md)
