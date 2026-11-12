---
article_id: af_928c4febdc156f49e7fb0876
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.Compression.buffer_eventually
---
# Buffers hold eventually

Take [fixed local data](../local-data/control/fixed-local-data.md). There are an index $i_1$ and a null sequence $(\epsilon'_i)$ of nonnegative reals such that the [buffer conditions](buffer-conditions.md) hold with $(\epsilon'_i)$ for every $i\ge i_1$.

*Proof sketch.*
1. $\overline B(0,t)$ is compact and lies in the open set $B(0,t')$ of $S^n$, so it has positive $d_S$-distance $\eta$ from $S^n\setminus B(0,t')$ ($d_S$ the metric of the [round sphere](../corner/round-sphere.md)). A retained cube $c$ contains a point $x$ with $f_T(x)\in\overline B(0,t)$, and its [sphere label](../chain-models/grid/sphere-labels.md) is $f_T$ of its [center](../chain-models/grid/cubical/grid-cube-center.md), which lies in the [closed cube](../chain-models/grid/cubical/grid-cube-realization.md) $|c|$ (the mesh $k_i\ge8$ is positive). So $d_S(s_b,f_T(x))\le\operatorname{diam}f_T(|c|)\le\epsilon_i$ by [chain-model estimates](../chain-models/grid/chain-model-estimates.md) (3), for the null sequence $(\epsilon_i)$ there. Once $\epsilon_i<\eta$, $s_b\in B(0,t')$. A retained dual cell $a^*$ carries the label of $a$, so the same bound applies.
2. Estimates (5) with $(v,v')=(t',u)$.
3. Estimates (4) with $v=u$ give a null sequence $(\epsilon^u_i)$; take $\epsilon'_i=\max(\epsilon^u_i,0)$, again null, and a larger bound preserves graph type.
Take $i_1$ the largest of the three thresholds.

## Sources
- HS paper, Section 10 (the radius bound for retained cells).

## Depends on

- [Buffer conditions](buffer-conditions.md)
- [Fixed local data](../local-data/control/fixed-local-data.md)

## Proof depends on

- [Chain-model estimates](../chain-models/grid/chain-model-estimates.md)
- [Sphere labels](../chain-models/grid/sphere-labels.md)
- [Round sphere](../corner/round-sphere.md)
- [Mesh sequence](../chain-models/grid/mesh-sequence.md)
- [The center of a grid cube](../chain-models/grid/cubical/grid-cube-center.md)
- [The closed cube](../chain-models/grid/cubical/grid-cube-realization.md)
