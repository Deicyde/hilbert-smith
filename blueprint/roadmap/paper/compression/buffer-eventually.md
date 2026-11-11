---
article_id: af_928c4febdc156f49e7fb0876
declaration: lemma
origin: bridged
statement: formalized
lean: HSP.Compression.buffer_eventually
---
# Buffers hold eventually

Take [fixed local data](../local-data/control/fixed-local-data.md) with buffer radii $t<u$, and put $t'=(t+u)/2$. Let $\mathcal P_i$ be the family of typed matrices of the [chain-model estimates](../chain-models/grid/chain-model-estimates.md). There are an index $i_1$ and a null sequence $(\epsilon'_i)$ such that, for every $i\ge i_1$:
1. every [retained cell](retained-cells.md) of $D_i$, and its dual, lies in $\mathcal B_i(t')$;
2. every $w\in\mathcal P_i$ satisfies $w\,\iota_{t'}=\iota_u\,w^{[t',u]}$;
3. every $w\in\mathcal P_i$ has [restriction](../chain-models/grid/buffers/restriction.md) $w^{[u]}$ of [graph type](../corner/actions/graph-type.md) equal to the type of $w$, with bound $\epsilon'_i$, for the [control labels](../chain-models/grid/buffers/control-labels.md).

Here $\mathcal B_i(v)$ are the [buffered cells](../chain-models/grid/buffers/buffered-cells.md) and $\iota_v$ the inclusion of their span, and the torus test map, sphere labels and control labels are those of the [buffered restriction](../chain-models/approximations/buffered-restriction.md) for the pinch radius $\rho$ of the fixed local data.

*Proof sketch.*
1. $\overline B(0,t)$ is compact and lies in the open set $B(0,t')$ of $S^n$, so it has positive $d_S$-distance $\eta$ from $S^n\setminus B(0,t')$ ($d_S$ the metric of the [round sphere](../corner/round-sphere.md)). A retained cube contains a point $x$ with $f_T(x)\in\overline B(0,t)$, and its [sphere label](../chain-models/grid/sphere-labels.md) is $f_T$ of a point of the same cube, so $d_S(s_b,f_T(x))\le\kappa_i\le\epsilon_i$ by estimates (3). Once $\epsilon_i<\eta$, $s_b\in B(0,t')$.
2. Estimates (5) with $(v,v')=(t',u)$.
3. Estimates (4) with $v=u$.
Take $i_1$ the largest of the three thresholds.

## Sources
- HS paper, Section 10 (the radius bound for retained cells).

## Depends on

- [Based inclusion](../chain-models/grid/buffers/based-inclusion.md)
- [The metric on the control space](../local-data/control/control-metric-space.md)
- [Retained cells](retained-cells.md)
- [Chain-model estimates](../chain-models/grid/chain-model-estimates.md)
- [Buffered cells](../chain-models/grid/buffers/buffered-cells.md)
- [Restriction](../chain-models/grid/buffers/restriction.md)
- [Control labels](../chain-models/grid/buffers/control-labels.md)
- [Graph-type matrices](../corner/actions/graph-type.md)
- [Buffered restriction](../chain-models/approximations/buffered-restriction.md)
- [Fixed local data](../local-data/control/fixed-local-data.md)

## Proof depends on

- [Sphere labels](../chain-models/grid/sphere-labels.md)
- [Round sphere](../corner/round-sphere.md)
