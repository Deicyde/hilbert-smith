---
declaration: theorem
origin: bridged
---
# Product homotopies

For $g,h\in G_i$ there are $B_{g,h}=B^T_{g,h}\otimes1_P$ of degree $+1$ with $a_ga_h-a_{g+h}=dB_{g,h}+B_{g,h}d$. There is $\mu'_i\to0$ such that every $B_{g,h}$ has sphere propagation at most $\mu'_i$. For $0<v<v'$, eventually $B_{g,h}^{[v,v']}$ has graph type $\chi_i(g+h)$ with bound $\mu'_i$, and $B\iota_v=\iota_{v'}B^{[v,v']}$.

*Proof sketch.* Write $\hat g=\widehat{r_i(g)}$. Use the carrier $\Gamma(c)=\mathrm{Box}(N_{h_i}(\hat g|\Gamma_{\hat h}(c)|\cup\widehat{g+h}|c|))$. It is monotone and contains $a_ga_hc$ and $a_{g+h}c$, and both maps preserve $\varepsilon$. Apply [carried homotopies](carried-homotopy.md). Set $p=\hat g\hat h(x_c)$ and $q=\widehat{g+h}(x_c)$. Every point $w$ of the carrier lies within $\lambda_i=O(\omega(h_i)+h_i)$ in each coordinate of the coordinate box spanned by $p$ and $q$. So $|w-x_c|^2\le|p-x_c|^2+|q-x_c|^2+o(1)\le8D^2+o(1)$, independent of $n$. If $|x_c|\ge3/8$, then since $3/8-2\sqrt2D>17/64$, $f_T=\infty$ at both ends. If $|x_c|<3/8$, property (5) puts the carrier within $\beta_i+o(1)$ of $r_i(g+h)x_c$. Then argue as for approximations.

## Sources
- HS paper, Section 9. New: box carriers, with no width induction and no track steps.
## Depends on
- [Group approximations](group-approx.md), [control labels](control-labels.md)
## Proof depends on
- [Carried homotopies](carried-homotopy.md), [box hull properties](box-hull-properties.md), [properties](completed-maps-properties.md), [graph type of approximations](approximations-graph-type.md)
