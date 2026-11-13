---
article_id: af_b9a5ee74694c838ba36ef08b
declaration: def
origin: background
statement: formalized
lean: HSP.Bounded.diag, HSP.Bounded.diagIso
---

# Diagonal morphisms of $C_\mathbb Z(A)$

For objects $M,N$ of the [bounded category](bounded-category.md) $C_\mathbb Z(A)$ and maps $d_n:M_n\to N_n$, the *diagonal morphism* $\operatorname{diag}(d):M\to N$ has entries $d_n$ at $(n,n)$ and $0$ elsewhere; it has propagation $0$. For $e_n:N_n\to P_n$, $\operatorname{diag}(e)\operatorname{diag}(d)=\operatorname{diag}(e_nd_n)$; the zero family gives $0$; $1_M=\operatorname{diag}(1_{M_n})$; for $d'_n:M_n\to N_n$, $\operatorname{diag}(d)+\operatorname{diag}(d')=\operatorname{diag}(d_n+d'_n)$; and, when $A$ is a [duality category](../../base/categories/duality-category.md), for the [induced duality](bounded-duality.md), $\operatorname{diag}(d)^*=\operatorname{diag}(d_n^*)$. If every $u_n:M_n\to N_n$ is an isomorphism, the *diagonal isomorphism* $\operatorname{diag}(u):M\cong N$ has inverse $\operatorname{diag}(u_n^{-1})$, by the composition rule and $1=\operatorname{diag}(1)$.

## Sources

- New: diagonal matrices of the bounded category.

## Depends on

- [The bounded category $C_\mathbb Z(A)$](bounded-category.md)

## Proof depends on

- [Small Q-linear category with strict duality](../../base/categories/duality-category.md)
- [The induced duality on $C_\mathbb Z(A)$](bounded-duality.md)
