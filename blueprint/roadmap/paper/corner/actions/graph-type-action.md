---
article_id: af_46ac22b0839af260e2d30f14
declaration: structure
origin: bridged
statement: formalized
lean: HSP.Corner.GraphAction
---

# Graph-type homotopy action

Take the [standing data](../standing-data.md). Let $(C,\phi)$ be a strict $N$-dimensional symmetric Poincaré complex in $\mathcal B_{\mathbf 1,Z}(T\times S^n)$, concentrated in $[0,N]$; its chain objects are objects of $\mathcal B_{\mathbf 1,Z}(T\times S^n)$, regarded in the idempotent completion with identity idempotents. Fix representative matrices $d_i$ and $\phi_i$ on its based modules, and write $d$ also for the differential of the [dual complex](../../l-theory/base/complexes/dual-complex.md) $C^{N-*}$, which is $(-1)^rd^*$ in degree $r$, with $d^*$ the dual differential.

A *graph-type homotopy action* of $\mathbf G$ on $(C,\phi)$ consists of one null sequence $(\delta_i)$ of reals and, for every $i$ and all $g,h\in G_i$ (written additively), matrices
- $A_g$ of degree $0$, with $A_0=1$;
- $B_{g,h}$ of degree $+1$;
- $V_g:C^{N-*}\to C$ of degree $+1$;

such that, for every $i$ and all $g,h\in G_i$, with the same bound $\delta_i$:
- $A_g$ and $V_g$ have [graph type](graph-type.md) $\chi_i(g)$, and $B_{g,h}$ has graph type $\chi_i(g+h)$;
- $dA_g-A_gd$ is an [exterior witness](exterior-witness.md) of type $\chi_i(g)$;
- $A_gA_h-A_{g+h}-dB_{g,h}-B_{g,h}d$ is an exterior witness of type $\chi_i(g+h)$;
- $A_g\phi-\phi A_{-g}^*-dV_g-V_gd$ is an exterior witness of type $\chi_i(g)$.

## Sources

- HS paper, Section 5 (relations) and Section 10 (compressed complex).

## Depends on

- [Standing data](../standing-data.md)
- [Graph-type matrices](graph-type.md)
- [Exterior witnesses](exterior-witness.md)
- [Strict symmetric Poincaré complex](../../l-theory/base/pairs/symmetric-poincare-complex.md)
- [Dual complex](../../l-theory/base/complexes/dual-complex.md)
- [Exterior quotient](../../categories/supports/exterior-quotient.md)
