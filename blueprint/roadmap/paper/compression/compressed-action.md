---
article_id: af_1f3125815327488e9cc7b3d7
declaration: lemma
origin: bridged
---
# The compressed action

Take [fixed local data](../local-data/control/fixed-local-data.md) with buffer radius $R$, and suppose the [control space](../local-data/control/control-space.md) $T$ is nonempty. Let $G_i=\mathbb Z/p^i$ for $i\ge1$ with $\chi_i$ reduction mod $p$, and let $0<s<R/\sqrt n$. Then $p$, $\mathbf G=(G_i,\chi_i)$, $T$ with the orbit metric and the cyclic action, $n$, $R$ and $s$ form [standing data](../corner/standing-data.md), and $(\hat A_g,\hat B_{g,h},\hat V_g)$ with the bound sequence $(\delta_i)$ of the [start index](start-index.md) is a [graph-type homotopy action](../corner/actions/graph-type-action.md) of $\mathbf G$ on $(C,\hat\varphi)$.

*Proof sketch.*
0. Standing data. $G_i=\mathbb Z/p^{a_i}$ with $a_i=i\ge1$, and reduction mod $p$ is onto $C_p$ because $p\mid p^i$. With the [orbit metric](../local-data/control/control-metric.md), $T$ is a metric space inducing the quotient topology ([the orbit metric metrizes the control space](../local-data/control/control-metric-properties.md)), compact ([the control space is compact](../local-data/control/control-space-compact.md)), and nonempty by hypothesis. The [cyclic action](../local-data/control/control-action.md) is [free](../local-data/control/control-action-free.md) and [isometric](../local-data/control/control-action-isometric.md). Finally $n\ge1$, $R>0$ (a buffer radius of the fixed local data) and $0<s<R/\sqrt n$.
1. Graph types. For $i\ge i_0$, $\hat A_g,\hat B_{g,h},\hat V_g$ are submatrices of $a_g^{[u]},B_{g,h}^{[u]},V_g^{[u]}$, so [buffers](buffer-eventually.md) (3) give the types $\chi_i(g)$, $\chi_i(g+h)$, $\chi_i(g)$ with bound $\delta_i$. Below $i_0$ they are zero.
2. $\hat A_0=1$ by [residuals](compressed-residuals.md) (4) (for $i<i_0$, $C_i$ is the zero module).
3. Defects. By residuals (1)-(3), each defect is a signed sum of words $p_2\alpha Q_1\beta\jmath_0$ of the [endpoint lemma](endpoint-lemma.md), of types $\chi_i(g)+0$; $\chi_i(g)+\chi_i(h)=\chi_i(g+h)$ and $\chi_i(g+h)+0$; $\chi_i(g)+0$ and $0-\chi_i(-g)=\chi_i(g)$. Each is an exterior witness of the required type with bound $\delta_i$, and so is their sum ([sums of witnesses](../corner/actions/witness-sum.md)). Below $i_0$ the defects are zero.

## Sources
- HS paper, Section 10.
## Depends on
- [Fixed local data](../local-data/control/fixed-local-data.md), [control space](../local-data/control/control-space.md), [compressed maps](compressed-maps.md), [graph-type action](../corner/actions/graph-type-action.md), [compressed Poincaré](compressed-poincare.md), [standing data](../corner/standing-data.md), [start index](start-index.md)
## Proof depends on
- [Orbit metric](../local-data/control/control-metric.md), [the orbit metric metrizes the control space](../local-data/control/control-metric-properties.md), [the control space is compact](../local-data/control/control-space-compact.md), [cyclic action](../local-data/control/control-action.md), [the cyclic action is free](../local-data/control/control-action-free.md), [the cyclic action is isometric](../local-data/control/control-action-isometric.md), [residuals](compressed-residuals.md), [endpoint lemma](endpoint-lemma.md), [buffers hold eventually](buffer-eventually.md), [sums of witnesses](../corner/actions/witness-sum.md)
