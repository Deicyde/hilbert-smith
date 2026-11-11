---
article_id: af_fafaa51e80fa19e209034aa6
declaration: theorem
origin: bridged
statement: formalized
lean: HSP.ChainModels.chainModel_estimates
---
# Chain-model estimates

Let $\mathcal P_i$ consist of the following matrices, each with a type in $C_p$: the differentials $d$ of $D_i$ and of $D_i^{N-*}$ (on the latter $d_r=(-1)^rd^*$), $\varphi_i,b_i,H_i,H'_i$ and $U_g$ (type $0$), $a_g$ (type $\chi_i(g)$), $a_g^*$ (type $-\chi_i(g)$), $B_{g,h}$ (type $\chi_i(g+h)$) and $V_g$ (type $\chi_i(g)$), for $g,h\in G_i$. There is a null sequence $(\epsilon_i)$ such that, for all $i$ and $g\in G_i$:
1. every $w\in\mathcal P_i$ has [sphere propagation](sphere-labels.md) at most $\epsilon_i$;
2. $a_0=1$, $a_gz_i=z_i$ and $\varepsilon a_g=\varepsilon$;
3. $\kappa_i=\max_c\operatorname{diam}_Sf_T(|c|)\le\epsilon_i$, the maximum over the cubes $c$ of $C(k_i)$;
4. for every $v>0$ there are $i_0$ and a null sequence $(\epsilon_i(v))$ such that, for $i\ge i_0$ and every $w\in\mathcal P_i$, the [restriction](restriction.md) $w^{[v]}$ has [graph type](../../corner/actions/graph-type.md) equal to the type of $w$, with bound $\epsilon_i(v)$, for the [control labels](control-labels.md);
5. for $0<v<v'$ there is $i_1$ such that $w\,\iota_v=\iota_{v'}w^{[v,v']}$ for all $i\ge i_1$ and $w\in\mathcal P_i$.

Here $G_i=\mathbb Z/p^i$ and $\chi_i$ is reduction mod $p$; $B_{g,h}$, $U_g$, $V_g$ are the ones chosen in [product homotopies](../approximations/product-homotopies.md), [isometry homotopies](../approximations/isometry-homotopies.md) and [adjoint homotopies](../approximations/adjoint-homotopies.md); each map is listed in every degree (the elements $\varphi_i,U_g,V_g$ of the structure complex by their components), with cells and duals labelled by their torus labels; sphere labels, buffers and control labels are those of the [buffered restriction](../approximations/buffered-restriction.md) for the torus test map of a radius $0<\rho<\rho_+$.

*Proof sketch.*
- Type-$0$ maps. $d$ has $d_\infty$-propagation at most $h_i/2$, $\varphi_i,b_i,H_i,H'_i$ at most $h_i$ ([Poincaré](chain-model-poincare.md) (3)), and $U_g$ at most $s_i+2h_i$ ([isometry homotopies](../approximations/isometry-homotopies.md)); transposes have the same propagation, and these bounds tend to $0$. Apply [buffered restriction](../approximations/buffered-restriction.md) (5).
- $a_g$, $B_{g,h}$, $V_g$: [graph type of approximations](../approximations/approximations-graph-type.md), [product homotopies](../approximations/product-homotopies.md), [adjoint homotopies](../approximations/adjoint-homotopies.md). $a_g^*$: buffered restriction (4).
- (2) [Group approximations](../approximations/group-approx.md), [fundamental cycle](../approximations/fundamental-cycle-fixed.md) and [carried group approximations](../approximations/group-approx-carried.md). (3) $f_T$ is uniformly continuous ([properties](../approximations/completed-maps-properties.md) (4)) and cubes have $d_\infty$-diameter $h_i$.
- (5) From (1) and buffered restriction (2).
Take $\epsilon_i$ the maximum of the finitely many null sequences above.

## Sources
- HS paper, Section 9 (closing choice of the bounds); these are the inputs of Section 10.
## Depends on
- [Poincaré](chain-model-poincare.md), [buffered restriction](../approximations/buffered-restriction.md), [group approximations](../approximations/group-approx.md), [product homotopies](../approximations/product-homotopies.md), [isometry homotopies](../approximations/isometry-homotopies.md), [adjoint homotopies](../approximations/adjoint-homotopies.md), [sphere labels](sphere-labels.md), [control labels](control-labels.md), [restriction](restriction.md), [graph-type matrices](../../corner/actions/graph-type.md)
## Proof depends on
- [Fundamental cycle](../approximations/fundamental-cycle-fixed.md), [carried group approximations](../approximations/group-approx-carried.md), [graph type of approximations](../approximations/approximations-graph-type.md), [properties](../approximations/completed-maps-properties.md)
