---
article_id: af_1af3099e61fc0ca361d11443
declaration: def
origin: bridged
statement: formalized
lean: HSP.ChainModels.adjointHomotopy
---

# The adjoint homotopy

Fix $0<\rho<\rho_+$. Let $g\in G_i$, $a=a_g$ and $a'=a_{-g}$ ([group approximations](group-approx.md)), $S=B_{-g,g}$ ([chosen product homotopies](chosen-product-homotopies.md)) and $U_g$ the [chosen isometry homotopy](chosen-isometry-homotopies.md). On $D_i^{N-*}$ (degree $r$ is $D^*_{N-r}$) let $K$ be the map of degree $+1$ given by $(-1)^rS^*$ on degree $r$. The *adjoint homotopy* is $V_g=a\varphi_iK+U_ga'^*$, a map of degree $+1$ from $D_i^{N-*}$ to $D_i$, that is, an element of $M(D_i)_{N+1}$; its component from $(D_i)_q^*$ to $(D_i)_p$, $p+q=N+1$, is $(-1)^{N-q}a_p\varphi_i(S_{q-1})^*+U_g(a'_q)^*$.

## Sources

- HS paper, Section 9; signs rechecked.

## Depends on

- [Group approximations](group-approx.md)
- [Chosen product homotopies](chosen-product-homotopies.md)
- [Chosen isometry homotopies](chosen-isometry-homotopies.md)
- [Chain-model duality](../grid/chain-model-duality.md)
