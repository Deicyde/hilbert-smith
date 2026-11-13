---
article_id: af_fafaa51e80fa19e209034aa6
declaration: theorem
origin: bridged
statement: formalized
lean: HSP.ChainModels.chainModel_estimates
---
# Chain-model estimates

Fix a radius $0<\rho<\rho_+$ and let $\mathcal P_i$ be the [family of chain-model matrices](../approximations/chain-model-family.md): the differentials of $D_i$ and $D_i^{N-*}$, $\varphi_i,b_i,H_i,H'_i,U_g$ of type $0$, $a_g$ of type $\chi_i(g)$, $a_g^*$ of type $-\chi_i(g)$, $B_{g,h}$ of type $\chi_i(g+h)$ and $V_g$ of type $\chi_i(g)$. There is a null sequence $(\epsilon_i)$ such that, for all $i$ and $g\in G_i$:
1. every $w\in\mathcal P_i$ has [sphere propagation](sphere-labels.md) at most $\epsilon_i$;
2. $a_0=1$, $a_gz_i=z_i$ and $\varepsilon a_g=\varepsilon$;
3. $\kappa_i=\max_c\operatorname{diam}_Sf_T(|c|)\le\epsilon_i$, the maximum over the cubes $c$ of $C(k_i)$;
4. for every $v>0$ there are $i_0$ and a null sequence $(\epsilon_i(v))$ such that, for $i\ge i_0$ and every $w\in\mathcal P_i$, the [restriction](buffers/restriction.md) $w^{[v]}$ has [graph type](../../corner/actions/graph-type.md) equal to the type of $w$, with bound $\epsilon_i(v)$, for the [control labels](buffers/control-labels.md);
5. for $0<v<v'$ there is $i_1$ such that $w\,\iota_v=\iota_{v'}w^{[v,v']}$ for all $i\ge i_1$ and $w\in\mathcal P_i$.

Here sphere labels, buffers and control labels are those of the [buffered restriction](../approximations/buffered-restriction.md) for the torus test map of radius $\rho$.

*Proof sketch.*
- Type-$0$ maps. $d$ has $d_\infty$-propagation at most $h_i/2$ ([propagation of the differential](poincare/chain-model-d-propagation.md)), $\varphi_i,b_i,H_i,H'_i$ at most $h_i$ ([Poincaré](chain-model-poincare.md) (3)), and $U_g$ at most $s_i+2h_i$ ([isometry homotopies](../approximations/isometry-homotopies.md)); transposes have the same propagation, and these bounds tend to $0$. Apply [buffered restriction](../approximations/buffered-restriction.md) (5).
- $a_g$, $B_{g,h}$, $V_g$: [graph type of approximations](../approximations/approximations-graph-type.md), [product homotopies](../approximations/product-homotopies.md), [adjoint homotopies](../approximations/adjoint-homotopies.md). $a_g^*$: buffered restriction (4).
- (2) [Group approximations](../approximations/group-approx.md), [fundamental cycle](../approximations/fundamental-cycle-fixed.md) and [carried group approximations](../approximations/group-approx-carried.md). (3) $f_T$ is uniformly continuous ([properties](../approximations/completed-maps-properties.md) (4)) and cubes have $d_\infty$-diameter $h_i$.
- (5) From (1) and buffered restriction (2).
Take $\epsilon_i$ the maximum of the finitely many null sequences above.

## Sources
- HS paper, Section 9 (closing choice of the bounds); these are the inputs of Section 10.
## Depends on

- [The closed cube](cubical/grid-cube-realization.md)
- [Sphere propagation](buffers/sphere-prop.md)
- [Fundamental cycle of the chain model](model/chain-model-fundamental.md)
- [Grid cubes](cubical/grid-cube.md)
- [The family of chain-model matrices](../approximations/chain-model-family.md)
- [Based inclusion](buffers/based-inclusion.md)
- [Buffered cells](buffers/buffered-cells.md)
- [The metric on the control space](../../local-data/control/control-metric-space.md)
- [Group approximations](../approximations/group-approx.md)
- [Control labels](buffers/control-labels.md)
- [Buffered restriction of a matrix](buffers/restriction.md)
- [Graph-type matrices](../../corner/actions/graph-type.md)
- [Torus test map](../approximations/torus-test-map.md)
- [Chain model](model/chain-model.md)
- [Mesh sequence](mesh-sequence.md)
- [Typed labelled matrices](../approximations/typed-matrix.md)
- [The augmentation of the chain model](poincare/chain-model-aug.md)
- [The torus](torus.md)
- [The round sphere](../../corner/round-sphere.md)
- [The category of based ℚ-vector spaces](../../l-theory/localization/products/bookkeeping/based-category.md)
- [Local datum](../../local-data/chart/local-datum.md)
- [The cyclic action on the control space](../../local-data/control/control-action.md)
- [The control space](../../local-data/control/control-space.md)

## Proof depends on

- [Approximations fix the fundamental cycle](../approximations/fundamental-cycle-fixed.md)
- [Carried group approximations](../approximations/group-approx-carried.md)
- [Graph type of approximations](../approximations/approximations-graph-type.md)
- [Properties of completed maps](../approximations/completed-maps-properties.md)
- [The chain model is Poincaré](chain-model-poincare.md)
- [Buffered restriction](../approximations/buffered-restriction.md)
- [Product homotopies](../approximations/product-homotopies.md)
- [Isometry homotopies](../approximations/isometry-homotopies.md)
- [Adjoint homotopies](../approximations/adjoint-homotopies.md)
- [Chosen product homotopies](../approximations/chosen-product-homotopies.md)
- [Chosen isometry homotopies](../approximations/chosen-isometry-homotopies.md)
- [The adjoint homotopy](../approximations/adjoint-homotopy.md)
- [Sphere labels](sphere-labels.md)
- [Cubical torus grid](cubical/cubical-torus-grid.md)
