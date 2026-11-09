---
declaration: lemma
origin: bridged
---
# The compressed action

With $G_i=\mathbb Z/p^i$ and $\chi_i$ reduction mod $p$, the family $(\hat A_g,\hat B_{g,h},\hat V_g)$ with bounds $(\delta_i)$ is a [graph-type homotopy action](../corner/graph-type-action.md) on $(C,\hat\varphi)$.

*Proof sketch.* Graph types come from [buffers](buffer-eventually.md) (3): $\chi_i(g)$, $\chi_i(g+h)$ and $\chi_i(g)$. $\hat A_0=1$. By [residuals](compressed-residuals.md) (1)-(3), the defects are sums of [endpoint](endpoint-lemma.md) words of types $\chi(g)+0$; $\chi(g)+\chi(h)$ and $\chi(g+h)+0$; and $\chi(g)+0$ and $0-\chi(-g)=\chi(g)$. Witnesses of one type stack through $W\oplus W$. Levels $i<i_0$ are zero.

## Sources
- HS paper, Section 10.
## Depends on
- [Compressed maps](compressed-maps.md), [graph-type action](../corner/graph-type-action.md), [compressed Poincaré](compressed-poincare.md)
## Proof depends on
- [Residuals](compressed-residuals.md), [endpoint lemma](endpoint-lemma.md)
