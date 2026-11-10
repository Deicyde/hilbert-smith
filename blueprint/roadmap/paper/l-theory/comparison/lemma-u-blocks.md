---
article_id: af_e7c862be1993bf2f4cde9d3d
declaration: lemma
origin: bridged
---

# Lemma U passes to the blocks

Let $\mathbf G=(G_i,\chi_i)$ be a group sequence, $i\in\mathbb N$ and $j\ge1$. For every object $P$ of $\mathrm{Kar}\,C_{\mathbb Z^j}(\mathrm{Free}(\mathbb Q[G_i]))$ there are objects $F,F'$ of $C_{\mathbb Z^j}(\mathrm{Free}(\mathbb Q[G_i]))$ with $P\oplus F\cong F'$. Here $\mathrm{Free}(\mathbb Q[G_i])$ is the [free category](../../categories/asymptotic/free-category.md).

*Proof sketch.* Let $\iota:\mathrm{Free}(\mathbb Q[G_i])\to\mathcal S_{\mathbf G}$ put an object in slot $i$ and the object $0$ in every other slot, and let $\pi:\mathcal S_{\mathbf G}\to\mathrm{Free}(\mathbb Q[G_i])$ be the $i$-th coordinate, with $\mathcal S_{\mathbf G}$ the [finite-support subcategory](../../categories/asymptotic/eventually-zero-subcategory.md). Both are additive, $\pi\iota=\mathrm{id}$, and the same holds after [bounded extension](../bounded/categories/bounded-functor.md) $j$ times and [completion](../base/categories/karoubi-functor.md). Given $P$, [Lemma U](lemma-u.md) for $\iota P$ gives $\iota P\oplus F\cong F'$; apply $\pi$: $P\oplus\pi F\cong\pi F'$.

## Sources

- New: retract argument.

## Depends on

- [Group sequence](../../categories/asymptotic/group-sequence.md)
- [Free category](../../categories/asymptotic/free-category.md)
- [Iterated bounded categories](../bounded/categories/iterated-bounded-category.md)

## Proof depends on

- [Lemma U](lemma-u.md)
- [Finite-support subcategory](../../categories/asymptotic/eventually-zero-subcategory.md)
- [Bounded extension of a duality functor](../bounded/categories/bounded-functor.md)
- [Completion of a duality functor](../base/categories/karoubi-functor.md)
