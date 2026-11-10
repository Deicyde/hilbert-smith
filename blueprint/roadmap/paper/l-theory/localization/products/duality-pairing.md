---
article_id: af_1c7fdf3eb219f94cf8c04af6
declaration: def
origin: background
---

# Duality pairings

Let $\mathcal B$, $\mathcal E$ and $\mathcal B''$ be [duality categories](../../base/categories/duality-category.md). A *duality pairing* $(\boxtimes,\kappa):\mathcal B\times\mathcal E\to\mathcal B''$ consists of

- a $\mathbb Q$-bilinear functor $\boxtimes:\mathcal B\times\mathcal E\to\mathcal B''$, and
- isomorphisms $\kappa_{N,V}:(N\boxtimes V)^*\to N^*\boxtimes V^*$, natural in both variables, $\kappa_{N,V}\circ(f\boxtimes g)^*=(f^*\boxtimes g^*)\circ\kappa_{N',V'}$ for $f:N\to N'$ and $g:V\to V'$, such that $(\kappa_{N,V})^*=\kappa_{N^*,V^*}$ as maps $(N^*\boxtimes V^*)^*\to N\boxtimes V$.

**Remark (not formalized).** The pairings used in this paper are the [box product](box-dual.md) $\mathrm{Kar}\,\mathcal B\times C_\mathbb Z(\mathbb Q)\to\mathrm{Kar}\,C_\mathbb Z(\mathcal B)$ and the [tensor product of based vector spaces](based-tensor.md) $\mathbb Q\times\mathbb Q\to\mathbb Q$.

## Sources

- [Ranicki 1980 I, §8, products](../../../../../sources/paper/ranicki-1980.md) [U]
- New: the data the product lemmas use, isolated so that one set of lemmas covers both pairings.

## Depends on

- [Small Q-linear category with strict duality](../../base/categories/duality-category.md)
