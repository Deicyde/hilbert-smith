---
article_id: af_78c8dec0591bb0b74d868493
declaration: lemma
origin: bridged
statement: formalized
lean: HSP.ChainModels.chainModel_d_propagation
---

# Propagation of the differential of the chain model

For every $i$, with cells of the [chain model](../chain-model.md) labelled at the centers of their cubes, the differential $d$ of $D_i$ has $d_\infty$-[propagation](../../../categories/asymptotic/propagation.md) at most $h_i/2=2/k_i$.

*Proof sketch.* Since $P$ has zero differential, the cells occurring in $d(c\otimes e)$ are $c'\otimes e$ with $c'$ a face of $c$. The center of a face differs from the center of $c$ by $2/k_i$ in the one coordinate where an edge became a vertex, and not at all in the others.

## Sources

- New: the explicit chain model of the cubical grid.

## Depends on

- [Chain model](../chain-model.md)
- [Propagation](../../../categories/asymptotic/propagation.md)

## Proof depends on

- [Cells of CP^2](../cp2/cp2-cells.md)
