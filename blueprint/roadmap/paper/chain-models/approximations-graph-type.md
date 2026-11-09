---
declaration: lemma
origin: bridged
---
# Graph type of approximations

There is $\mu_i\to0$ such that every $a_g$ ($g\in G_i$) has sphere propagation at most $\mu_i$. For $0<v<v'$ there is $i_0$ such that, for $i\ge i_0$, $a_g\iota_v=\iota_{v'}a_g^{[v,v']}$ and $a_g^{[v,v']}$ has [graph type](../corner/graph-type.md) $\chi_i(g)$ with bound $\mu_i$.

*Proof sketch.* A target cell of $c$ lies within $\omega(h_i)+4h_i$ of $\widehat{r_i(g)}(x_c)$. Since $f_T\widehat{r_i(g)}=f_T$, the modulus $\omega_f$ bounds the sphere propagation. Then use [buffered restriction](buffered-restriction.md). On $Z^+\subseteq B(0,1)$, $\widehat{r_i(g)}=r_i(g)\cdot{}$, and $\pi(r_i(g)x)=\chi_i(g)\cdot\pi(x)$ by the [action](../local-data/control/control-action.md) and [algebra](../local-data/control/representatives-algebra.md) (3). [Uniform continuity](../local-data/control/projection-uniform.md) bounds $d_T$.

## Sources
- HS paper, Section 9.
## Depends on
- [Group approximations](group-approx.md), [control labels](control-labels.md), [graph-type matrices](../corner/graph-type.md)
## Proof depends on
- [Buffered restriction](buffered-restriction.md), [properties](completed-maps-properties.md), [projection uniform](../local-data/control/projection-uniform.md)
