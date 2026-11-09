---
article_id: af_e7c862be1993bf2f4cde9d3d
declaration: lemma
origin: bridged
---

# Lemma U passes to the blocks

$U(\mathcal S)$ implies $U(\mathrm{Free}\,\mathbb Q[G_i])$ for every $i$.

*Proof sketch.* Let $\iota:\mathrm{Free}\,\mathbb Q[G_i]\to\mathcal S$ put a module in slot $i$ and a zero object in every other slot, and let $\pi:\mathcal S\to\mathrm{Free}\,\mathbb Q[G_i]$ be the $i$-th coordinate. Both are additive, $\pi\iota=\mathrm{id}$, and the same holds after [bounded extension](../bounded/categories/bounded-functor.md) $j$ times and completion. Given $P$, apply $U(\mathcal S)$ to $\iota P$ to get $\iota P\oplus F\cong F'$, then apply $\pi$: $P\oplus\pi F\cong\pi F'$.

## Sources

- New: retract argument.

## Depends on

- [Lemma U](lemma-u.md)
- [Finite-support sum](../base/groups/finite-support-sum.md)

## Proof depends on

- [Bounded extension of a duality functor](../bounded/categories/bounded-functor.md)
- [Completion of a duality functor](../base/categories/karoubi-functor.md)
