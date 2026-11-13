---
article_id: af_f770a5fe73bf622d7217e323
declaration: def
origin: bridged
statement: formalized
lean: HSP.ChainModels.chainModelFamily
---

# The family of chain-model matrices

The family consists of [typed labelled matrices](typed-matrix.md): matrices $u:\mathbb Q^B\to\mathbb Q^{B'}$ between finite sets of cells $B,B'$ with torus labels, each with a type $c\in C_p$.

Let $G_i=\mathbb Z/p^i$, let $\chi_i:G_i\to C_p$ be reduction mod $p$, and $N=n+4$. The family $\mathcal P_i$ of the [chain model](../grid/model/chain-model.md) $D_i$ consists of the following typed labelled matrices, for $g,h\in G_i$:
- of type $0$: the differentials $d$ of $D_i$ and of $D_i^{N-*}$ (on the latter $d_r=(-1)^rd^*$), the maps $\varphi_i,b_i$ of the [chain-model duality](../grid/chain-model-duality.md), $H_i,H'_i$ from [Poincaré](../grid/chain-model-poincare.md), and the [chosen isometry homotopies](chosen-isometry-homotopies.md) $U_g$;
- the [group approximations](group-approx.md) $a_g$, of type $\chi_i(g)$, and their transposes $a_g^*$, of type $-\chi_i(g)$;
- the [chosen product homotopies](chosen-product-homotopies.md) $B_{g,h}$, of type $\chi_i(g+h)$, for a radius $0<\rho<\rho_+$;
- the [adjoint homotopies](adjoint-homotopy.md) $V_g$, of type $\chi_i(g)$.

Each map is listed in every degree, and the elements $\varphi_i,U_g,V_g$ of the structure complex by their components. Cells of $D_i$ and their duals in $D_i^{N-*}$ carry their torus labels; a dual cell has the label of its cell.

## Sources

- New: the family of matrices controlled in the chain-model estimates (HS paper, Section 9).

## Depends on

- [Typed labelled matrices](typed-matrix.md)
- [Local datum](../../local-data/chart/local-datum.md)

## Proof depends on

- [The adjoint homotopy](adjoint-homotopy.md)
- [Chosen isometry homotopies](chosen-isometry-homotopies.md)
- [Chosen product homotopies](chosen-product-homotopies.md)
- [Group approximations](group-approx.md)
- [Tensor product of based complexes](../grid/based-complex-tensor.md)
- [Chain-model duality](../grid/chain-model-duality.md)
- [The cellular chain complex of CP^2](../grid/cp2/cp2-complex.md)
- [Cubical torus grid](../grid/cubical/cubical-torus-grid.md)
- [Mesh sequence](../grid/mesh-sequence.md)
- [Torus labels of chain-model cells](../grid/model/chain-model-label.md)
- [Chain model](../grid/model/chain-model.md)
- [The dual homotopy of the chain model](../grid/poincare/chain-model-h-dual.md)
- [The homotopy of the chain model](../grid/poincare/chain-model-h.md)
- [The torus](../grid/torus.md)
- [Small Q-linear category with strict duality](../../l-theory/base/categories/duality-category.md)
- [Dual complex](../../l-theory/base/complexes/dual-complex.md)
- [Based vector spaces](../../l-theory/localization/products/based-vector-spaces.md)
- [The category of based ℚ-vector spaces](../../l-theory/localization/products/bookkeeping/based-category.md)
