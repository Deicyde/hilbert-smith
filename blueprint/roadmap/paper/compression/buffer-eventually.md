---
article_id: af_928c4febdc156f49e7fb0876
declaration: lemma
origin: bridged
---
# Buffers hold eventually

Let $\gamma>0$ be the $d_S$-distance between $\overline B(0,t')$ and $S^n\setminus B(0,u)$. Let $\mathcal P_i$ consist of $d$, $\delta$, $\varphi_i,b_i,H_i,H'_i$ (type $0$), $a_g$ (type $\chi_i(g)$), $a_g^*$ (type $-\chi_i(g)$), $B_{g,h}$ (type $\chi_i(g+h)$) and $V_g$ (type $\chi_i(g)$), for $g,h\in G_i$. There is a null sequence $(\epsilon'_i)$ and, for all large $i$:
1. every retained cell of $D_i$ lies in $\mathcal B_i(t')$;
2. every $w\in\mathcal P_i$ has sphere propagation less than $\gamma$;
3. every nonzero entry of $w\in\mathcal P_i$ between two cells of $\mathcal B_i(u)$ satisfies the graph-type condition of its type with bound $\epsilon'_i$.

*Proof sketch.* (1) A retained cube contains a point of $K_t$, so its label lies within $\kappa_i\le\epsilon_i$ of $\overline B(0,t)$. That set has positive $d_S$-distance from $S^n\setminus B(0,t')$. (2) Estimates (1). (3) Take $(v,v')=(u,u+1)$ in the estimates. Such an entry is an entry of $w^{[u,u+1]}$. For $a_g^*$ and $\delta=\pm d^*$, the transposed entry is an entry of $a_g$ or $d$ between the same two cells, and the transpose has the inverse type by the graph-type calculus.

## Sources
- HS paper, Section 10 (the radius bound for retained cells).
## Depends on
- [Retained cells](retained-cells.md), [control labels](../chain-models/grid/control-labels.md)
## Proof depends on
- [Chain-model estimates](../chain-models/grid/chain-model-estimates.md), [graph-type matrices](../corner/actions/graph-type.md), [compact neighbourhoods](../local-data/chart/test-map-proper.md)
