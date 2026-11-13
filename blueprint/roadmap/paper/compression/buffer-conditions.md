---
article_id: af_f767f27c9c58326282b3178e
declaration: def
origin: bridged
statement: formalized
lean: HSP.Compression.BuffersHold
---
# Buffer conditions

Take [fixed local data](../local-data/control/fixed-local-data.md) with buffer radii $t<u$, and put $t'=(t+u)/2$. Let $\mathcal P_i$ be the [family of chain-model matrices](../chain-models/approximations/chain-model-family.md) for the radius $\rho$ of the fixed local data, and let $(\epsilon'_i)$ be a sequence of reals. The *buffer conditions* hold at the index $i$ (with $(\epsilon'_i)$) if:
1. every [retained cell](retained-cells.md) of $D_i$, and its dual, lies in $\mathcal B_i(t')$;
2. every $w\in\mathcal P_i$ satisfies $w\,\iota_{t'}=\iota_u\,w^{[t',u]}$;
3. every $w\in\mathcal P_i$ has [restriction](../chain-models/grid/buffers/restriction.md) $w^{[u]}$ of [graph type](../corner/actions/graph-type.md) equal to the type of $w$, with bound $\epsilon'_i$, for the [control labels](../chain-models/grid/buffers/control-labels.md).

Here $\mathcal B_i(v)$ are the [buffered cells](../chain-models/grid/buffers/buffered-cells.md) and $\iota_v$ the [based inclusion](../chain-models/grid/buffers/based-inclusion.md) of their span, and the torus test map, sphere labels and control labels are those of the [buffered restriction](../chain-models/approximations/buffered-restriction.md) for the pinch radius $\rho$ of the fixed local data.

## Sources
- HS paper, Section 10 (the radius bound for retained cells).

## Depends on

- [Fixed local data](../local-data/control/fixed-local-data.md)

## Proof depends on

- [The family of chain-model matrices](../chain-models/approximations/chain-model-family.md)
- [Typed labelled matrices](../chain-models/approximations/typed-matrix.md)
- [Based inclusion](../chain-models/grid/buffers/based-inclusion.md)
- [Buffered cells](../chain-models/grid/buffers/buffered-cells.md)
- [Control labels](../chain-models/grid/buffers/control-labels.md)
- [Restriction](../chain-models/grid/buffers/restriction.md)
- [Torus labels of dual cells](../chain-models/grid/model/chain-model-dual-label.md)
- [Torus labels of chain-model cells](../chain-models/grid/model/chain-model-label.md)
- [Chain model](../chain-models/grid/model/chain-model.md)
- [Retained cells](retained-cells.md)
- [Graph-type matrices](../corner/actions/graph-type.md)
- [The round sphere](../corner/round-sphere.md)
- [The category of based ℚ-vector spaces](../l-theory/localization/products/bookkeeping/based-category.md)
- [The cyclic action on the control space](../local-data/control/control-action.md)
- [The metric on the control space](../local-data/control/control-metric-space.md)
- [The control space](../local-data/control/control-space.md)
