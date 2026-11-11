---
article_id: af_733959f85426bccbb6c61e03
declaration: theorem
origin: bridged
statement: formalized
lean: HSP.ChainModels.product_homotopies
---
# Product homotopies

For $g,h\in G_i$ there are $B_{g,h}=B^T_{g,h}\otimes1_P$ of degree $+1$ with $a_ga_h-a_{g+h}=dB_{g,h}+B_{g,h}d$, and a null sequence $(\mu'_i)$, such that every $B_{g,h}$ has [sphere propagation](../grid/sphere-labels.md) at most $\mu'_i$ and, for every $v>0$, $B_{g,h}^{[v]}$ has [graph type](../../corner/actions/graph-type.md) $\chi_i(g+h)$ with bound $\mu'_i$ for the [control labels](../grid/buffers/control-labels.md). Here $G_i=\mathbb Z/p^i$, $\chi_i$ is reduction mod $p$, and the sphere and control labels are those of the [buffered restriction](buffered-restriction.md) for the torus test map of a radius $0<\rho<\rho_+$.

*Proof sketch.* Write $\hat g=\widehat{r_i(g)}$. Use the carrier $\Gamma(c)=\mathrm{Box}(N_{h_i}(\hat g|\Gamma_{\hat h}(c)|\cup\widehat{g+h}|c|))$. It is nested under faces and contains $a_ga_hc$ and $a_{g+h}c$ ([carried group approximations](group-approx-carried.md)), and both maps preserve $\varepsilon$. Apply [carried homotopies](../grid/carried-homotopy.md). Set $p=\hat g\hat h(x_c)$ and $q=\widehat{g+h}(x_c)$. By [box hull properties](../grid/box-hull-properties.md) (2), every point $w$ of the carrier lies, in each coordinate, within $\lambda_i=O(\omega(h_i)+h_i)$ of the interval between the coordinates of $p$ and $q$. So $|w-x_c|^2\le|p-x_c|^2+|q-x_c|^2+o(1)\le5D^2+o(1)$, using [properties](completed-maps-properties.md) (2). If $|x_c|\ge3/8$, then since $3/8-2\sqrt2D>17/64$, $f_T=\infty$ at $x_c$ and on the whole carrier (properties (4)). If $|x_c|<3/8$, properties (5) put the carrier within $\beta_i+o(1)$ of $r_i(g+h)x_c$, and $f_T(r_i(g+h)x_c)=f_T(x_c)$ by properties (3). This bounds the sphere propagation. For two buffered cells, the lifts lie in $U^+$ ([buffered restriction](buffered-restriction.md) (1)), $r_i(g+h)\tilde x_c\in U^+$ by [invariance of the test regions](../../local-data/chart/test-region-invariant.md), and the control coordinate is bounded as in [graph type of approximations](approximations-graph-type.md), with $\chi_i(g+h)$ in place of $\chi_i(g)$.

## Sources
- HS paper, Section 9. New: box carriers, with no width induction and no track steps.
## Depends on
- [Cubical torus grid](../grid/cubical/cubical-torus-grid.md)
- [The metric on the control space](../../local-data/control/control-metric-space.md)
- [Group approximations](group-approx.md), [tensoring with the identity of the cells of CP^2](tensor-one-p.md), [sphere labels](../grid/sphere-labels.md), [control labels](../grid/buffers/control-labels.md), [restriction](../grid/buffers/restriction.md), [graph-type matrices](../../corner/actions/graph-type.md), [buffered restriction](buffered-restriction.md)
## Proof depends on
- [Carried homotopies](../grid/carried-homotopy.md), [carried group approximations](group-approx-carried.md), [box hull properties](../grid/box-hull-properties.md), [properties](completed-maps-properties.md), [test region invariant](../../local-data/chart/test-region-invariant.md), [graph type of approximations](approximations-graph-type.md)
