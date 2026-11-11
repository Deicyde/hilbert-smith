---
article_id: af_f429bc8df81b00dd937a1270
declaration: lemma
origin: bridged
statement: formalized
lean: HSP.ChainModels.adjoint_homotopies
---
# Adjoint homotopies

Let $g\in G_i$, $a=a_g$, $a'=a_{-g}$ and $S=B_{-g,g}$, so that $a'a-1=dS+Sd$. On $D_i^{N-*}$ (degree $r$ is $D^*_{N-r}$, with differential $d_r=(-1)^rd^*$) let $K$ be the map of degree $+1$ given by $(-1)^rS^*$ on degree $r$, and put $V_g=a\varphi_iK+U_ga'^*$. Then: Here $B_{-g,g}$ and $U_g$ are the ones chosen in [product homotopies](product-homotopies.md) and [isometry homotopies](isometry-homotopies.md), and labels, $\chi_i$ and $\rho$ are as in product homotopies.
1. $dV_g+V_gd=a_g\varphi_i-\varphi_ia_{-g}^*$;
2. there is a null sequence $(\mu''_i)$ such that $V_g$ has [sphere propagation](../grid/sphere-labels.md) at most $\mu''_i$ and, for every $v>0$, $V_g^{[v]}$ has [graph type](../../corner/actions/graph-type.md) $\chi_i(g)$ with bound $\mu''_i$ for all large $i$.

*Proof sketch.* (1) Dualizing gives $a^*a'^*-1=S^*d^*+d^*S^*$, and the sign $(-1)^r$ turns this into $dK+Kd=1-a^*a'^*$ on $D_i^{N-*}$. Since $\varphi_i$ and $a$ are chain maps, $d(a\varphi_iK)+a\varphi_iKd=a\varphi_i-a\varphi_ia^*a'^*$. By [isometry homotopies](isometry-homotopies.md), $d(U_ga'^*)+U_ga'^*d=(a\varphi_ia^*-\varphi_i)a'^*$, and the sum telescopes. (2) Sphere propagation adds under composition. For the types: $K$ is $\pm$ the transpose of $S$, which has type $\chi_i(-g+g)=0$; $\varphi_i$ and $U_g$ have type $0$; $a$ has type $\chi_i(g)$; and $a'^*$ has type $-\chi_i(-g)=\chi_i(g)$. Each factor has small sphere propagation, so for radii $v<v'<v''$ and large $i$ it commutes with the buffers ([buffered restriction](buffered-restriction.md) (2)), and its square restrictions to $\mathcal B_i(v')$ and $\mathcal B_i(v'')$ have the stated types: for $a$ by [graph type of approximations](approximations-graph-type.md); for $\varphi_i$ and $U_g$ by buffered restriction (5), since their torus propagation tends to $0$ ([Poincaré](../grid/chain-model-poincare.md) (3), isometry homotopies); for $K$ by [product homotopies](product-homotopies.md) and buffered restriction (4); for $a'^*$ by graph type of approximations and buffered restriction (4). Buffered restriction (3), applied twice, composes them, and (4) adds the two terms.

## Sources
- HS paper, Section 9; signs rechecked.
## Depends on
- [Product homotopies](product-homotopies.md), [isometry homotopies](isometry-homotopies.md), [group approximations](group-approx.md), [sphere labels](../grid/sphere-labels.md), [restriction](../grid/restriction.md), [graph-type matrices](../../corner/actions/graph-type.md), [buffered restriction](buffered-restriction.md)
## Proof depends on
- [graph type of approximations](approximations-graph-type.md), [Poincaré](../grid/chain-model-poincare.md)
