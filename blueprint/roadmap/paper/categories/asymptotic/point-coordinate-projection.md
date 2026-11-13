---
article_id: af_ffd37352ca8f49d86cdf19fe
declaration: def
origin: bridged
statement: formalized
lean: HSP.PCat.proj
---

# Coordinate projection of the sequence category

Let $\mathbf G=(G_i,\chi_i)$ be a [group sequence](group-sequence.md) and $i\in\mathbb N$. The *coordinate projection* $\pi_i:\mathcal P_{\mathbf G}\to\mathrm{Free}(\mathbb Q[G_i])$ from the [sequence category](point-sequence-category.md) to the [free category](free-category.md) sends an object $(n_j)$ to $n_i$ and a morphism $(u_j)$ to $u_i$. It is a [duality functor](../../l-theory/base/categories/duality-functor.md) with $\xi=\mathrm{id}$, so it is strict.

## Sources

- HS paper, Section 3

## Depends on

- [Group sequence](group-sequence.md)
- [Sequence category](point-sequence-category.md)
- [Free category of a finite group](free-category.md)
- [Duality functor](../../l-theory/base/categories/duality-functor.md)

## Proof depends on

- [Small Q-linear category with strict duality](../../l-theory/base/categories/duality-category.md)
