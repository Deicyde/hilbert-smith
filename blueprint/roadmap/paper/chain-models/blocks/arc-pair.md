---
article_id: af_8f87da11ff2e6575dd2d269d
declaration: def
origin: background
---
# Arc pair

Let $m\ge1$ and let $I_m$ be the arc complex: vertices $[0],\dots,[m]$, edges $e_0,\dots,e_{m-1}$, $de_w=[w+1]-[w]$, $\varepsilon[w]=1$. Its boundary is $C=\mathbb Q[0]\oplus\mathbb Q[m]$ in degree $0$, with based inclusion $j:C\to I_m$, and $\pi:I_m\to I_m/C$ is the based projection onto the span of the other cells. The *arc pair* is $(j:C\to I_m,\varphi_I,\varphi_C)$, with $\varphi_I\in M(I_m)_1$ and $\varphi_C\in M(C)_0$ given by
- $\varphi_I(e_w^*)=\tfrac12([w]+[w+1])$ and $\varphi_I([w]^*)=\tfrac12(e_{w-1}+e_w)$, where a term with a missing edge is omitted;
- $\varphi_C([0]^*)=-[0]$ and $\varphi_C([m]^*)=[m]$.

Its relative data, with $(I_m/C)^{1-*}$ the [dual complex](../../l-theory/base/complexes/dual-complex.md), are $\theta_I=\varphi_I\pi^*:(I_m/C)^{1-*}\to I_m$ and the following maps:
- $b:I_m\to(I_m/C)^{1-*}$: $b([w])=e_w^*$ for $w<m$, $b([m])=e_{m-1}^*$, $b(e_w)=[w+1]^*$ for $w\le m-2$, $b(e_{m-1})=0$;
- $K_1=K+\tfrac12Hb$ on $I_m$ and $K_2=\tfrac12bH$ on $(I_m/C)^{1-*}$. Here $H:(I_m/C)^{1-*}\to I_m$ has degree $+1$, $H(e_w^*)=e_w$ and $H([w]^*)=0$; and $K:I_m\to I_m$ has degree $+1$, $K([m])=-e_{m-1}$, and $K$ is zero on the other cells.

The fundamental chain is $z_I=\sum_{w<m}e_w$, with $dz_I=[m]-[0]$.

## Sources
- New: the boundary analogue of circle duality.

## Depends on
- [Strict Poincaré pair](../../l-theory/base/pairs/poincare-pair.md), [structure complex](../../l-theory/base/complexes/structure-complex.md), [dual complex](../../l-theory/base/complexes/dual-complex.md)
