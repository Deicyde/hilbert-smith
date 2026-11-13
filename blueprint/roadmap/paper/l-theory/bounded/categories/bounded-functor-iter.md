---
article_id: af_867c90eca4e62adf927c701f
declaration: def
origin: background
statement: formalized
lean: HSP.Bounded.mapIter
---

# Iterated bounded extension

For a duality functor $(F,\xi):\mathcal A\to\mathcal A'$, the *iterated bounded extension* $C_{\mathbb Z^j}(F,\xi):C_{\mathbb Z^j}(\mathcal A)\to C_{\mathbb Z^j}(\mathcal A')$ of [iterated bounded categories](iterated-bounded-category.md) is $(F,\xi)$ for $j=0$ and the [bounded extension](bounded-functor.md) $C_\mathbb Z(C_{\mathbb Z^{j-1}}(F,\xi))$ for $j\ge1$.

## Sources

- New: the $j$-fold iterate of the bounded extension.

## Depends on

- [Iterated bounded categories](iterated-bounded-category.md)
- [Small Q-linear category with strict duality](../../base/categories/duality-category.md)
- [Duality functor](../../base/categories/duality-functor.md)

## Proof depends on

- [The bounded category $C_\mathbb Z(A)$](bounded-category.md)
- [The induced duality on $C_\mathbb Z(A)$](bounded-duality.md)
- [Bounded extension of a duality functor](bounded-functor.md)
