---
article_id: af_6c518e1e454c93d409dc0f13
declaration: lemma
origin: bridged
statement: formalized
lean: HSP.ChainModels.bufferedRestriction
---
# Buffered restriction

1. If $b\in\mathcal B_i(v)$, then $\tilde x_b\in U^+$.
2. For $0<v<v'$ there is $\eta>0$ such that every matrix $u$ with sphere propagation less than $\eta$ satisfies $u\iota_v=\iota_{v'}u^{[v,v']}$.
3. Let $0<v<v'$, and let $u,u'$ be composable matrices with $u\iota_v=\iota_{v'}u^{[v,v']}$, such that $u^{[v']}$ has graph type $c$ with bound $\epsilon$ and $u'^{[v']}$ has graph type $c'$ with bound $\epsilon'$. Then $(u'u)^{[v]}$ has graph type $c+c'$ with bound $\epsilon+\epsilon'$.
4. If $u^{[v]}$ has graph type $c$ with bound $\epsilon$, then $(u^*)^{[v]}$ has graph type $-c$ with bound $\epsilon$. If $u^{[v]}$ and $u'^{[v]}$ have graph type $c$ with bound $\epsilon$, so does $(u+u')^{[v]}$.
5. For every $\epsilon>0$ there is $t>0$ such that, for all $i$ and $v>0$, every matrix $u$ with $d_\infty$-propagation at most $t$ in torus labels has sphere propagation at most $\epsilon$, and $u^{[v]}$ has graph type $0$ with bound $\epsilon$.

Graph types are those of [graph-type matrices](../../corner/actions/graph-type.md) for the [control labels](../grid/buffers/control-labels.md) in $T\times S^n$, with $C_p$ written additively. Here $0<\rho<\rho_+$ is the radius of the torus test map $f_T$. All items hold for any finite sets of cells with torus labels $x_b$, such as the cells of $D_i$ and of $D_i^{N-*}$, with $\mathcal B(v)$, $\iota_v$, the sphere labels $f_T(x_b)$ and the control labels defined from $x_b$ as for $D_i$; in (1), $b$ may be any point of $\mathbb T^n$ with $f_T(b)\in B(0,v)$.

*Proof sketch.* (1) $s_b\in B(0,v)\subseteq\overline B(0,v)$, and [preimages](../../local-data/chart/test-map-proper.md) with $C=\overline B(0,v)$ give $\tilde x_b\in U^+$; $U^+\subseteq Z^+$ by the definition of the test regions. (2) $\overline B(0,v)$ is compact and lies in the open set $B(0,v')$, so it has positive $d_S$-distance $\eta$ from $S^n\setminus B(0,v')$. A nonzero entry from $b\in\mathcal B_i(v)$ then lands in $\mathcal B_i(v')$. (3) $(u'u)^{[v]}=(p_vu'\iota_{v'})(p_{v'}u\iota_v)$, and the two factors are submatrices of $u'^{[v']}$ and $u^{[v']}$, since $\mathcal B_i(v)\subseteq\mathcal B_i(v')$. A nonzero entry from $b$ to $b''$ needs a cell $b'$ with $d(\lambda b',c\cdot\lambda b)\le\epsilon$ and $d(\lambda b'',c'\cdot\lambda b')\le\epsilon'$; since $C_p$ acts isometrically, $d(\lambda b'',(c+c')\cdot\lambda b)\le\epsilon'+\epsilon$. (4) $(u^*)^{[v]}=(u^{[v]})^*$ because $\iota_v^*=p_v$, and a cell and its dual have the same label; $d(\lambda b,-c\cdot\lambda b')=d(c\cdot\lambda b,\lambda b')$. A nonzero entry of a sum is a nonzero entry of a summand. (5) $f_T$ is uniformly continuous from $d_\infty$ to $d_S$ ([properties](completed-maps-properties.md) (4)). For two cells of $\mathcal B_i(v)$ at torus distance $t<1$, the lifts lie in $U^+\subseteq B(0,1)$ by (1) and differ by at most $\sqrt n\,t$, and the [uniform continuity of the orbit map](../../local-data/control/projection-uniform.md) bounds $d_T$.

## Sources
- HS paper, Section 9 (the eventual definition of target labels).
## Depends on
- [Buffered sphere labels](../grid/buffers/buffered-sphere-labels.md)
- [The metric on the control space](../../local-data/control/control-metric-space.md)
- [The lift](../torus/lift.md)
- [Buffered restriction of a matrix](../grid/buffers/restriction.md), [sphere labels](../grid/sphere-labels.md), [graph-type matrices](../../corner/actions/graph-type.md), [control labels](../grid/buffers/control-labels.md), [buffered cells](../grid/buffers/buffered-cells.md), [based inclusion](../grid/buffers/based-inclusion.md), [open test region](../../local-data/chart/open-test-region.md), [test region](../../local-data/chart/test-region.md), [torus test map](torus-test-map.md)
## Proof depends on
- [Preimages](../../local-data/chart/test-map-proper.md), [test region](../../local-data/chart/test-region.md), [open test region](../../local-data/chart/open-test-region.md), [test region bounded](../../local-data/chart/test-region-bounded.md), [properties](completed-maps-properties.md), [projection uniform](../../local-data/control/projection-uniform.md)
