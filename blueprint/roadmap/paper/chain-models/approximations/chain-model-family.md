---
article_id: af_f770a5fe73bf622d7217e323
declaration: def
origin: bridged
statement: formalized
lean: HSP.ChainModels.chainModelFamily
---

# The family of chain-model matrices

A *typed labelled matrix* is a matrix $u:\mathbb Q^B\to\mathbb Q^{B'}$ between finite sets of cells $B,B'$ with torus labels $x_b,x'_{b'}\in\mathbb T^n$, together with a type $c\in C_p$.

Let $G_i=\mathbb Z/p^i$, let $\chi_i:G_i\to C_p$ be reduction mod $p$, and $N=n+4$. The family $\mathcal P_i$ of the [chain model](../grid/chain-model.md) $D_i$ consists of the following typed labelled matrices, for $g,h\in G_i$:
- of type $0$: the differentials $d$ of $D_i$ and of $D_i^{N-*}$ (on the latter $d_r=(-1)^rd^*$), the maps $\varphi_i,b_i$ of the [chain-model duality](../grid/chain-model-duality.md), $H_i,H'_i$ from [Poincaré](../grid/chain-model-poincare.md), and the [chosen isometry homotopies](chosen-isometry-homotopies.md) $U_g$;
- the [group approximations](group-approx.md) $a_g$, of type $\chi_i(g)$, and their transposes $a_g^*$, of type $-\chi_i(g)$;
- the [chosen product homotopies](chosen-product-homotopies.md) $B_{g,h}$, of type $\chi_i(g+h)$, for a radius $0<\rho<\rho_+$;
- the [adjoint homotopies](adjoint-homotopy.md) $V_g$, of type $\chi_i(g)$.

Each map is listed in every degree, and the elements $\varphi_i,U_g,V_g$ of the structure complex by their components. Cells of $D_i$ and their duals in $D_i^{N-*}$ carry their torus labels; a dual cell has the label of its cell.

## Sources

- New: the family of matrices controlled in the chain-model estimates (HS paper, Section 9).

## Depends on

- [Chain model](../grid/chain-model.md), [chain-model duality](../grid/chain-model-duality.md), [Poincaré](../grid/chain-model-poincare.md), [group approximations](group-approx.md), [chosen isometry homotopies](chosen-isometry-homotopies.md), [chosen product homotopies](chosen-product-homotopies.md), [adjoint homotopy](adjoint-homotopy.md)
