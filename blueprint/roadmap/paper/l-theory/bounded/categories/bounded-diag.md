---
article_id: af_b9a5ee74694c838ba36ef08b
declaration: def
origin: background
statement: formalized
lean: HSP.Bounded.diag
---

# Diagonal morphisms of $C_\mathbb Z(A)$

For objects $M,N$ of the [bounded category](bounded-category.md) $C_\mathbb Z(A)$ and maps $d_n:M_n\to N_n$, the *diagonal morphism* $\operatorname{diag}(d):M\to N$ has entries $d_n$ at $(n,n)$ and $0$ elsewhere; it has propagation $0$. For $e_n:N_n\to P_n$, $\operatorname{diag}(e)\operatorname{diag}(d)=\operatorname{diag}(e_nd_n)$; the zero family gives $0$; and $1_M=\operatorname{diag}(1_{M_n})$.

## Sources

- New: diagonal matrices of the bounded category.

## Depends on

- [The bounded category $C_\mathbb Z(A)$](bounded-category.md)
