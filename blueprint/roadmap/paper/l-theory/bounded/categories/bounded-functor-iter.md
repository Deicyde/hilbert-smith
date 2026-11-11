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

- [Bounded extension of a duality functor](bounded-functor.md), [iterated bounded categories](iterated-bounded-category.md)
