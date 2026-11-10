---
article_id: af_02adcbd6d51c3607afea42ef
declaration: def
origin: bridged
---
# Compressed complex

Take [fixed local data](../local-data/control/fixed-local-data.md), with control space $T$, and the [start index](start-index.md) $i_0$. The *compressed complex* $C$ is the object of $\mathcal A_{\mathbf 1}(T\times S^n)$ (the [asymptotic category](../categories/asymptotic/asymptotic-category.md) for the trivial group sequence) whose based module $C_i$ is spanned by $\mathrm{Ret}_i$, the [retained cells](retained-cells.md) of $D_i$, with the [control labels](../chain-models/grid/control-labels.md) $\lambda(b)=(\pi(\tilde x_b),s_b)$, for $i\ge i_0$, and is the zero module for $i<i_0$.

Notation: $\mathrm{pr}_i:D_i\to C_i$ and $\mathrm{in}_i:C_i\to D_i$ are the based projection and inclusion, and $Q_i=1-\mathrm{in}_i\mathrm{pr}_i$; on cochains they are $\mathrm{in}_i^*$, $\mathrm{pr}_i^*$ and $Q_i^*$.

**Remark (not formalized).** Retained cells lie in $\mathcal B_i(t')$ for $i\ge i_0$ ([buffers](buffer-eventually.md) (1)), so $\tilde x_b\in Z^+$ by [buffered restriction](../chain-models/approximations/buffered-restriction.md) (1) and the label needs no point of $T$. Only retained cells get labels; the full $D_i$ is never an object over $T\times S^n$.

## Sources
- HS paper, Section 10 (the quotient by far simplices). New: the zero levels, and labels only on retained cells.

## Depends on

- [Start index](start-index.md)
- [Retained cells](retained-cells.md)
- [Control labels](../chain-models/grid/control-labels.md)
- [Asymptotic category](../categories/asymptotic/asymptotic-category.md)
- [Buffers hold eventually](buffer-eventually.md)
- [Buffered restriction](../chain-models/approximations/buffered-restriction.md)
