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

- [Chain model](../grid/model/chain-model.md)
- [Structure complex](../../l-theory/base/complexes/structure-complex.md)
- [Based vector spaces](../../l-theory/localization/products/based-vector-spaces.md)
- [The category of based ℚ-vector spaces](../../l-theory/localization/products/bookkeeping/based-category.md)
- [Local datum](../../local-data/chart/local-datum.md)

## Proof depends on

- [Chosen isometry homotopies](chosen-isometry-homotopies.md)
- [Chosen product homotopies](chosen-product-homotopies.md)
- [Group approximations](group-approx.md)
- [Chain-model duality](../grid/chain-model-duality.md)
- [Small Q-linear category with strict duality](../../l-theory/base/categories/duality-category.md)
