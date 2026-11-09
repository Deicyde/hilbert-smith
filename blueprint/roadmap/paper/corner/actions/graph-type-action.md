---
article_id: af_46ac22b0839af260e2d30f14
declaration: def
origin: bridged
---

# Graph-type homotopy action

Let $(C,\phi)$ be a strict $N$-dimensional symmetric Poincaré complex in $\mathcal B_{\mathbf 1,Z}(T\times S^n)$, concentrated in $[0,N]$. Fix representative matrices $d_i$ and $\phi_i$ on its based modules.

A *graph-type homotopy action* of $\mathbf G$ on $(C,\phi)$ consists of one null sequence $(\delta_i)$ of reals and, for every $i$ and all $g,h\in G_i$, matrices
- $A_g$ of degree $0$, with $A_1=1$;
- $B_{g,h}$ of degree $+1$;
- $V_g:C^{N-*}\to C$ of degree $+1$;

such that, for every $i$ and all $g,h\in G_i$, with the same bound $\delta_i$:
- $A_g$ and $V_g$ have [graph type](graph-type.md) $\chi_i(g)$, and $B_{g,h}$ has graph type $\chi_i(gh)$;
- $dA_g-A_gd$ is an [exterior witness](exterior-witness.md) of type $\chi_i(g)$;
- $A_gA_h-A_{gh}-dB_{g,h}-B_{g,h}d$ is an exterior witness of type $\chi_i(gh)$;
- $A_g\phi-\phi A_{g^{-1}}^*-dV_g-V_gd^{N-*}$ is an exterior witness of type $\chi_i(g)$.

## Sources

- HS paper, Section 5 (relations) and Section 10 (compressed complex).

## Depends on

- [Graph-type matrices](graph-type.md)
- [Exterior witnesses](exterior-witness.md)
- [Strict symmetric Poincaré complex](../../l-theory/base/pairs/symmetric-poincare-complex.md)
