---
article_id: af_ea2a080113bfc55e94567824
declaration: lemma
origin: background
---
# Arc duality

For the [arc pair](arc-pair.md) $(j:C\to I_m,\varphi_I,\varphi_C)$, with $d$ the differential of each complex (on dual complexes $d_r=(-1)^rd^*$):
1. $T\varphi_I=\varphi_I$, $\partial\varphi_I=j_\%\varphi_C$, $T\varphi_C=\varphi_C$ and $\partial\varphi_C=0$; $(\varphi_C)_\natural$ is an isomorphism, so $(C,\varphi_C)$ is a strict $0$-dimensional symmetric Poincaré complex;
2. $\theta_I$ and $b$ are chain maps, $\theta_Ib-1=dK_1+K_1d$ and $b\theta_I-1=dK_2+K_2d$;
3. the arc pair is a strict $1$-dimensional symmetric Poincaré pair;
4. with every cell and its dual labelled at the cell's center, $\varphi_I,\varphi_C,\theta_I,b,K_1,K_2$ have propagation at most the mesh;
5. $\varepsilon\theta_I(e_w^*)=1=e_w^*(z_I)$ for every edge $e_w$.

*Proof sketch.* Write $\varphi$ for the unsymmetrized map $e_w^*\mapsto[w]$, $[w]^*\mapsto e_{w-1}$ (omitted for $w=0$), and $H(e_w^*)=e_w$, $H([w]^*)=0$ on $I_m^{1-*}$. Then $\varphi_I=\varphi+\tfrac12(dH+Hd)$. (1) A direct check gives $\partial\varphi=j_\%\varphi_C$: the defect is $-[0]$ at $[0]^*$ and $[m]$ at $[m]^*$. The correction $\tfrac12\partial H$ is a boundary, so $\partial\varphi_I=\partial\varphi$. $T\varphi_I=\varphi_I$ is read off the symmetric formulas. (2) $\theta_I$ is a chain map because $j^*\pi^*=0$. On $(I_m/C)^{1-*}$, $\varphi$ includes a copy of $I_{m-1}$ and $b$ retracts onto it: $b\varphi\pi^*=1$ and $\varphi\pi^*b-1=dK+Kd$. Add the corrections $\tfrac12Hb$ and $\tfrac12bH$, using that $b$ is a chain map. (3) $j$ is a based inclusion, so it is degreewise split injective with quotient $\pi$; by (2), $\theta_I$ is a chain homotopy equivalence, and the [split pair criterion](../../l-theory/base/pairs/split-pair-criterion.md) shows that the pair map is one. With (1) this is the [definition](../../l-theory/base/pairs/poincare-pair.md). (4) Read off the formulas. (5) $\varphi_I(e_w^*)=\tfrac12([w]+[w+1])$.

## Sources
- New. Replaces the cone-section argument of HS paper, Section 12.
## Depends on
- [Arc pair](arc-pair.md), [strict Poincaré pair](../../l-theory/base/pairs/poincare-pair.md), [propagation](../../categories/asymptotic/propagation.md)
## Proof depends on
- [Split pair criterion](../../l-theory/base/pairs/split-pair-criterion.md), [strict symmetric Poincaré complex](../../l-theory/base/pairs/symmetric-poincare-complex.md)
