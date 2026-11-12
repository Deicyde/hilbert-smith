---
article_id: af_467e958c9105136b1ca3cc5e
declaration: def
origin: cited
statement: formalized
lean: HSP.symLine.str
---

# Structure of the symmetric line

Let $\Lambda$ be the [symmetric line](symmetric-line.md). Its *structure* is the element $\lambda\in M(\Lambda)_1$ of the [structure complex](../../base/complexes/structure-complex.md) whose components are
$$\lambda_0:\Lambda_1^*\to\Lambda_0,\ \ e^*_{n+1/2}\mapsto\tfrac12(v_n+v_{n+1}),\qquad \lambda_1:\Lambda_0^*\to\Lambda_1,\ \ v_n^*\mapsto\tfrac12(e_{n-1/2}+e_{n+1/2}),$$
all other components being zero. Both maps have propagation $1$.

## Sources

- [Ranicki 1992, §16-17, products with the line](../../../../../sources/paper/ranicki-1992.md) [U]
- HS paper, Section 7 (the averaged diagonal $\tfrac12(1+T)$ of cellular chains)
- New: the explicit formulas, in the conventions of [Structure complex](../../base/complexes/structure-complex.md).

## Depends on

- [The symmetric line](symmetric-line.md)
- [Structure complex](../../base/complexes/structure-complex.md)
- [The induced duality on $C_\mathbb Z(A)$](../../bounded/categories/bounded-duality.md)
