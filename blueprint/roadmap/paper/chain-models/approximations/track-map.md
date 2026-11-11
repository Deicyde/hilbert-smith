---
article_id: af_055e692db90e1d1153e6fdad
declaration: def
origin: bridged
statement: formalized
lean: HSP.ChainModels.trackMap
---
# Track maps

For $a,b,c\in\mathbb Z_p$ and $t\in[0,1]$, put $L_{a,b,c,t}=(1-t)\,\widehat a\widehat b+t\,\widehat c$ on $\mathbb R^n$. This is the identity off $B(0,3/2)$, so it induces the map $x\mapsto q(L_{a,b,c,t}(\tilde x))$ of $\mathbb T^n$, also written $L_{a,b,c,t}$. The family $\mathcal F$ consists of all these maps of $\mathbb T^n$; it contains each $\widehat a=L_{a,0,a,t}$ and $\mathrm{id}=L_{0,0,0,t}$.

## Sources
- HS paper, Section 9 (raw product tracks).
## Depends on
- [The lift](../torus/lift.md)
- [The quotient map](../torus/proj.md)
- [Completed map](completed-map.md)
- [The torus](../grid/torus.md)

## Proof depends on

- [The quotient map inverts the lift](../torus/proj-lift.md)
