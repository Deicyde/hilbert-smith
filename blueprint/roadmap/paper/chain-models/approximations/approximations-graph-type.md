---
article_id: af_da447357291253954e826466
declaration: lemma
origin: bridged
---
# Graph type of approximations

There is a null sequence $(\mu_i)$ such that, for all $i$, $g\in G_i$ and $v>0$, $a_g$ has [sphere propagation](../grid/sphere-labels.md) at most $\mu_i$ and $a_g^{[v]}$ has [graph type](../../corner/actions/graph-type.md) $\chi_i(g)$ with bound $\mu_i$ for the [control labels](../grid/control-labels.md).

*Proof sketch.* Let $L=\widehat{r_i(g)}$. By [carried group approximations](group-approx-carried.md) and [chain approximations exist](chain-approx-exists.md), a target cell $b'$ of a cell $b$ satisfies $d_\infty(x_{b'},Lx_b)\le\omega(h_i)+4h_i$. Since $f_TL=f_T$ ([properties](completed-maps-properties.md) (3)), $d_S(s_{b'},s_b)\le\omega_f(\omega(h_i)+4h_i)$. If $b,b'\in\mathcal B_i(v)$, the lifts $\tilde x_b,\tilde x_{b'}$ lie in $U^+\subseteq Z^+\subseteq B(0,1)$ ([buffered restriction](buffered-restriction.md) (1), [boundedness](../../local-data/chart/test-region-bounded.md)). There $L$ acts as $r_i(g)$, and $r_i(g)\tilde x_b\in U^+$ by [invariance of the test regions](../../local-data/chart/test-region-invariant.md), so $|\tilde x_{b'}-r_i(g)\tilde x_b|\le\sqrt n(\omega(h_i)+4h_i)$. By the [action](../../local-data/control/control-action.md) and [algebra of the representatives](../../local-data/control/representatives-algebra.md) (3), $\pi(r_i(g)\tilde x_b)=\chi_i(g)\cdot\pi(\tilde x_b)$, and the [uniform continuity of the orbit map](../../local-data/control/projection-uniform.md) bounds $d_T(\pi\tilde x_{b'},\chi_i(g)\cdot\pi\tilde x_b)$ by a null sequence.

## Sources
- HS paper, Section 9.
## Depends on
- [Group approximations](group-approx.md), [sphere labels](../grid/sphere-labels.md), [control labels](../grid/control-labels.md), [restriction](../grid/restriction.md), [graph-type matrices](../../corner/actions/graph-type.md)
## Proof depends on
- [Carried group approximations](group-approx-carried.md), [chain approximations exist](chain-approx-exists.md), [buffered restriction](buffered-restriction.md), [properties](completed-maps-properties.md), [test region bounded](../../local-data/chart/test-region-bounded.md), [test region invariant](../../local-data/chart/test-region-invariant.md), [control action](../../local-data/control/control-action.md), [representatives algebra](../../local-data/control/representatives-algebra.md), [projection uniform](../../local-data/control/projection-uniform.md)
