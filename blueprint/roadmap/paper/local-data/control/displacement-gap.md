---
article_id: af_fac8ee1e3d65c7385fac1698
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.LocalDatum.exists_displacement_gap
---

# A uniform displacement gap

For a local datum there is $\varepsilon_T>0$ such that $d_T(t,c\cdot t)\ge\varepsilon_T$ for all $t\in T$ and all $c\ne0$ in $C_p$.

*Proof sketch.* For each $c\ne0$ the function $t\mapsto d_T(t,c\cdot t)$ is continuous, because the action is isometric, and positive, because the action is free. On the compact $T$ it attains a positive minimum $\varepsilon_c$; if $T=\varnothing$, take $\varepsilon_c=1$. Let $\varepsilon_T$ be the least of the finitely many $\varepsilon_c$.

## Sources

- New: offered for the later chapters in case they need disjoint translates

## Depends on

- [The cyclic action on the control space](control-action.md)
- [The orbit metric on the control space](control-metric.md)

## Proof depends on

- [The cyclic action is free](control-action-free.md)
- [The cyclic action is isometric](control-action-isometric.md)
- [The orbit metric metrizes the control space](control-metric-properties.md)
- [The control space is compact](control-space-compact.md)
