---
article_id: af_02adcbd6d51c3607afea42ef
declaration: def
origin: bridged
statement: formalized
lean: HSP.Compression.compressed
---
# Compressed complex

Take [fixed local data](../local-data/control/fixed-local-data.md), with control space $T$, and the [start index](start-index.md) $i_0$. The *compressed complex* $C$ has in each degree $r$ the object $C_r$ of $\mathcal A_{\mathbf 1}(T\times S^n)$ (the [asymptotic category](../categories/asymptotic/asymptotic-category.md) for the trivial group sequence) whose based module $(C_r)_i$ is spanned by the cells of $\mathrm{Ret}_i$, the [retained cells](retained-cells.md) of $D_i$, in $(D_i)_r$, in their order in $D_i$, with the [control labels](../chain-models/grid/buffers/control-labels.md) $\lambda(b)=(\pi(\tilde x_b),s_b)$, for $i\ge i_0$, and is the zero module for $i<i_0$.

For $i\ge i_0$ the retained cells lie in $\mathcal B_i(t')$ by the [buffer conditions](buffer-conditions.md) (1), which hold for every $i\ge i_0$ by the choice of the start index; so the control label of [control labels](../chain-models/grid/buffers/control-labels.md) is defined on them, and no point of $T$ is needed. Only retained cells get labels; the full $D_i$ is never an object over $T\times S^n$.

## Sources
- HS paper, Section 10 (the quotient by far simplices). New: the zero levels, and labels only on retained cells.

## Depends on

- [The metric on the control space](../local-data/control/control-metric-space.md)
- [Asymptotic category](../categories/asymptotic/asymptotic-category.md)
- [Fixed local data](../local-data/control/fixed-local-data.md)
- [The trivial group sequence](../categories/asymptotic/trivial-group-sequence.md)
- [The round sphere](../corner/round-sphere.md)
- [The cyclic action on the control space](../local-data/control/control-action.md)
- [The control space](../local-data/control/control-space.md)

## Proof depends on

- [The family of chain-model matrices](../chain-models/approximations/chain-model-family.md)
- [Typed labelled matrices](../chain-models/approximations/typed-matrix.md)
- [Based inclusion](../chain-models/grid/buffers/based-inclusion.md)
- [Buffered cells](../chain-models/grid/buffers/buffered-cells.md)
- [Control labels](../chain-models/grid/buffers/control-labels.md)
- [Buffered restriction of a matrix](../chain-models/grid/buffers/restriction.md)
- [Torus labels of dual cells](../chain-models/grid/model/chain-model-dual-label.md)
- [Torus labels of chain-model cells](../chain-models/grid/model/chain-model-label.md)
- [Chain model](../chain-models/grid/model/chain-model.md)
- [Buffer conditions](buffer-conditions.md)
- [Buffers hold eventually](buffer-eventually.md)
- [Retained cells](retained-cells.md)
- [Start index](start-index.md)
- [Graph-type matrices](../corner/actions/graph-type.md)
- [The category of based ℚ-vector spaces](../l-theory/localization/products/bookkeeping/based-category.md)
