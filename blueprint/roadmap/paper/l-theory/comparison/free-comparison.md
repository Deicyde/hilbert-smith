---
article_id: af_05c38e0f1dac8049f5f9ede0
declaration: theorem
origin: bridged
---

# Point comparison for the free categories

Let $\mathbf G=(G_i,\chi_i)$ be a group sequence. Then $\mathrm{cls}:L^p_k(\mathrm{Free}(\mathbb Q[G_i]))\to\mathbb L_k(\mathrm{Free}(\mathbb Q[G_i]))$ is bijective for all $k$ and $i$, where $\mathrm{Free}(\mathbb Q[G_i])$ is the [free category](../../categories/asymptotic/free-category.md).

*Proof sketch.* [Lemma U passes to the blocks](lemma-u-blocks.md) gives the hypothesis of the [stable criterion](../bounded/categories/lower-k-vanishing-criterion.md), so $K_{-j}(\mathrm{Free}(\mathbb Q[G_i]))=0$ for $j\ge1$. Then apply [the decoration comparison](decoration-comparison.md).

## Sources

- New: E2 plus the hypothesis.

## Depends on

- [Group sequence](../../categories/asymptotic/group-sequence.md)
- [Free category](../../categories/asymptotic/free-category.md)
- [Ultimate L-group](../ultimate/groups/ultimate-l-group.md)

## Proof depends on

- [Lemma U passes to the blocks](lemma-u-blocks.md)
- [Stable criterion for vanishing lower $K$](../bounded/categories/lower-k-vanishing-criterion.md)
- [Decoration comparison](decoration-comparison.md)
