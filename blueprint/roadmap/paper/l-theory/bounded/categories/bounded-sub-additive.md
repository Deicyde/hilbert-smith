---
article_id: af_12b12514665f5cd6162580e7
declaration: instance
origin: background
statement: formalized
lean: HSP.Bounded.isDualAdditive_sub
---

# The bounded subcategory is closed under sums and duals

If $U\subset A$ is a full additive subcategory closed under the duality, so is the [bounded subcategory](bounded-sub.md) $C_\mathbb Z(U)\subset C_\mathbb Z(A)$, for [the induced duality](bounded-duality.md).

*Proof sketch.* The constant family at a zero object of $U$ is a zero object of $C_\mathbb Z(A)$. A sum of $V,W\in C_\mathbb Z(U)$ is assembled from degreewise biproducts $V_n\oplus W_n$ in $U$, with diagonal inclusions and projections of propagation $0$. The dual has $(M^*)_n=(M_n)^*$, which lies in $U$.

## Sources

- New: closure properties of $C_\mathbb Z(U)$.

## Depends on

- [The bounded subcategory](bounded-sub.md), [the induced duality](bounded-duality.md), [additive subcategory closed under duality](../../base/categories/dual-additive-subcategory.md)
