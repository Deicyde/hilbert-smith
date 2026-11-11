---
article_id: af_2910b717ced7f467a60d21c8
declaration: lemma
origin: cited
statement: formalized
lean: HSP.symLine.str_T_and_cycle
proof: formalized
---

# The symmetric line is a symmetric complex

The [structure](symmetric-line-structure.md) $\lambda$ of the [symmetric line](symmetric-line.md) satisfies $T\lambda=\lambda$ and $\partial\lambda=0$, so $(\Lambda,\lambda)$ is a strict $1$-dimensional symmetric complex.

*Proof sketch.* Both identities are direct checks. $(T\lambda)_0=\lambda_1^*$ and $(T\lambda)_1=\lambda_0^*$, since the sign $(-1)^{r(1-r)}$ is $1$; and $\lambda_1^*(e^*_{m+1/2})=\tfrac12(v_m+v_{m+1})=\lambda_0(e^*_{m+1/2})$, because $e_{m+1/2}$ occurs in $\lambda_1(v_n^*)$ exactly for $n=m,m+1$. The only component of $\partial\lambda$ that can be nonzero is $(\partial\lambda)_0=d\lambda_1+\lambda_0d^*$. Since $d^*(v_n^*)=e^*_{n-1/2}-e^*_{n+1/2}$,
$$d\lambda_1(v_n^*)=\tfrac12(v_{n+1}-v_{n-1}),\qquad \lambda_0d^*(v_n^*)=\tfrac12(v_{n-1}+v_n)-\tfrac12(v_n+v_{n+1})=\tfrac12(v_{n-1}-v_{n+1}),$$
which sum to zero.

## Sources

- [Ranicki 1992, §16-17, products with the line](../../../../../sources/paper/ranicki-1992.md) [U]
- New: the two checks, in the conventions of [Structure complex](../../base/complexes/structure-complex.md) and [The involution T](../../base/complexes/structure-involution.md).

## Depends on

- [Structure of the symmetric line](symmetric-line-structure.md)
- [Structure complex](../../base/complexes/structure-complex.md)
- [The involution T](../../base/complexes/structure-involution.md)

## Proof depends on

- [The symmetric line](symmetric-line.md)
- [The induced duality on $C_\mathbb Z(A)$](../../bounded/categories/bounded-duality.md)
