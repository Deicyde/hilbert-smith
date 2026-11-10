---
article_id: af_c4b5a190314c76eeb69d5cd1
declaration: lemma
origin: background
---

# Additivity on ultimate L

For duality functors $F,G:\mathcal A\to\mathcal B$, $(F\oplus G)_*=F_*+G_*$ on $\mathbb L_k(\mathcal A)$, with $F\oplus G$ as in [Sums of functors](../../base/groups/sum-of-functors.md).

*Proof sketch.* At level $j$, [Bounded extension of a sum of functors](bounded-sum-extension.md) gives a unitary natural isomorphism $C_{\mathbb Z^j}(F\oplus G)\cong C_{\mathbb Z^j}F\oplus C_{\mathbb Z^j}G$. [Unitary invariance](../../base/groups/unitary-invariance.md) and [Sums of functors](../../base/groups/sum-of-functors.md) give $(C_{\mathbb Z^j}(F\oplus G))_*=(C_{\mathbb Z^j}F)_*+(C_{\mathbb Z^j}G)_*$. Conclude with [The induced map at each level](induced-map-level.md); every element of the colimit comes from a finite level ([Every element comes from a finite level](level-exhaustive.md)).

## Sources

- New: levelwise.

## Depends on

- [Induced map on ultimate L](induced-map.md)
- [Sums of functors](../../base/groups/sum-of-functors.md)

## Proof depends on

- [Bounded extension of a sum of functors](bounded-sum-extension.md)
- [Unitary invariance](../../base/groups/unitary-invariance.md)
- [Sums of functors](../../base/groups/sum-of-functors.md)
- [The induced map at each level](induced-map-level.md)
- [Every element comes from a finite level](level-exhaustive.md)
