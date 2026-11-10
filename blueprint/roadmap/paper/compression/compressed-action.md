---
article_id: af_1f3125815327488e9cc7b3d7
declaration: lemma
origin: bridged
---
# The compressed action

Suppose the control space $T$ is nonempty, take $G_i=\mathbb Z/p^i$ for $i\ge1$ with $\chi_i$ reduction mod $p$, and take any $s$ with $0<s<R/\sqrt n$, so that these data with $T$ and $R$ form [standing data](../corner/standing-data.md). Then $(\hat A_g,\hat B_{g,h},\hat V_g)$ with the bound sequence $(\delta_i)$ of the [start index](start-index.md) is a [graph-type homotopy action](../corner/actions/graph-type-action.md) of $\mathbf G=(G_i,\chi_i)$ on $(C,\hat\varphi)$.

*Proof sketch.*
1. Graph types. For $i\ge i_0$, $\hat A_g,\hat B_{g,h},\hat V_g$ are submatrices of $a_g^{[u]},B_{g,h}^{[u]},V_g^{[u]}$, so [buffers](buffer-eventually.md) (3) give the types $\chi_i(g)$, $\chi_i(g+h)$, $\chi_i(g)$ with bound $\delta_i$. Below $i_0$ they are zero.
2. $\hat A_0=1$ by [residuals](compressed-residuals.md) (4) (for $i<i_0$, $C_i$ is the zero module).
3. Defects. By residuals (1)-(3), each defect is a signed sum of words $p_2\alpha Q_1\beta\jmath_0$ of the [endpoint lemma](endpoint-lemma.md), of types $\chi_i(g)+0$; $\chi_i(g)+\chi_i(h)=\chi_i(g+h)$ and $\chi_i(g+h)+0$; $\chi_i(g)+0$ and $0-\chi_i(-g)=\chi_i(g)$. Each is an exterior witness of the required type with bound $\delta_i$, and so is their sum ([sums of witnesses](../corner/actions/witness-sum.md)). Below $i_0$ the defects are zero.

## Sources
- HS paper, Section 10.
## Depends on
- [Compressed maps](compressed-maps.md), [graph-type action](../corner/actions/graph-type-action.md), [compressed Poincaré](compressed-poincare.md), [standing data](../corner/standing-data.md), [start index](start-index.md)
## Proof depends on
- [Residuals](compressed-residuals.md), [endpoint lemma](endpoint-lemma.md), [buffers hold eventually](buffer-eventually.md), [sums of witnesses](../corner/actions/witness-sum.md)
