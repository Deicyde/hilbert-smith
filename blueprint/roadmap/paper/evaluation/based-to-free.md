---
article_id: af_6c8a75992dda925306cfc099
declaration: def
origin: background
statement: formalized
lean: HSP.Evaluation.basedToFree
---

# Based vector spaces over the trivial group

The functor from [based vector spaces](../l-theory/localization/products/based-vector-spaces.md) to the [free category](../categories/asymptotic/free-category.md) $\mathrm{Free}(\mathbb Q[\{1\}])$ of the one-point group sends $\mathbb Q^d$ to $\mathbb Q[\{1\}]^d$, with basis $\{1\}\times\{1,\dots,d\}$, and a $d'\times d$ matrix $u$ to the matrix with the same entries on these bases, which is equivariant because the group is trivial. With $\xi=\mathrm{id}$ it is a strict [duality functor](../l-theory/base/categories/duality-functor.md), since both dualities are the transpose.

## Sources

- New: based vector spaces are the free modules over the trivial group.

## Depends on

- [Based vector spaces](../l-theory/localization/products/based-vector-spaces.md)
- [Free category of a finite group](../categories/asymptotic/free-category.md)
- [Duality functor](../l-theory/base/categories/duality-functor.md)
