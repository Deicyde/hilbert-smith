---
article_id: af_e14d11d332d9e89abdc3731a
declaration: def
origin: cited
---

# The symmetric line

Let $\mathbb Q$ be the duality category of [based vector spaces](based-vector-spaces.md). The *symmetric line* is the complex $\Lambda$ in $C_\mathbb Z(\mathbb Q)$ with $\Lambda_0$ equal to $\mathbb Qv_n$ in position $n$, $\Lambda_1$ equal to $\mathbb Qe_{n+1/2}$ in position $n$, every other $\Lambda_r$ a zero object, and $d e_{n+1/2}=v_{n+1}-v_n$ (propagation $1$), together with the structure $\lambda\in M(\Lambda)_1$ whose components are
$$\lambda_0:\Lambda_1^*\to\Lambda_0,\ \ e^*_{n+1/2}\mapsto\tfrac12(v_n+v_{n+1}),\qquad \lambda_1:\Lambda_0^*\to\Lambda_1,\ \ v_n^*\mapsto\tfrac12(e_{n-1/2}+e_{n+1/2}),$$
all other components being zero. Both maps have propagation $1$. The structure satisfies $T\lambda=\lambda$ and $\partial\lambda=0$, so $(\Lambda,\lambda)$ is a strict $1$-dimensional symmetric complex.

Both identities are direct checks. $(T\lambda)_0=\lambda_1^*$ and $(T\lambda)_1=\lambda_0^*$, since the sign $(-1)^{r(1-r)}$ is $1$; and $\lambda_1^*(e^*_{m+1/2})=\tfrac12(v_m+v_{m+1})=\lambda_0(e^*_{m+1/2})$, because $e_{m+1/2}$ occurs in $\lambda_1(v_n^*)$ exactly for $n=m,m+1$. The only component of $\partial\lambda$ that can be nonzero is $(\partial\lambda)_0=d\lambda_1+\lambda_0d^*$. Since $d^*(v_n^*)=e^*_{n-1/2}-e^*_{n+1/2}$,
$$d\lambda_1(v_n^*)=\tfrac12(v_{n+1}-v_{n-1}),\qquad \lambda_0d^*(v_n^*)=\tfrac12(v_{n-1}+v_n)-\tfrac12(v_n+v_{n+1})=\tfrac12(v_{n-1}-v_{n+1}),$$
which sum to zero.

## Sources

- [Ranicki 1992, §16-17, products with the line](../../../../../sources/paper/ranicki-1992.md) [U]
- HS paper, Section 7 (the averaged diagonal $\tfrac12(1+T)$ of cellular chains)
- New: the explicit formulas and the two checks, in the conventions of [Structure complex](../../base/complexes/structure-complex.md) and [The involution T](../../base/complexes/structure-involution.md).

## Depends on

- [Based vector spaces](based-vector-spaces.md)
- [The bounded category](../../bounded/categories/bounded-category.md)
- [The induced duality on $C_\mathbb Z(A)$](../../bounded/categories/bounded-duality.md)
- [Structure complex](../../base/complexes/structure-complex.md)
- [The involution T](../../base/complexes/structure-involution.md)
