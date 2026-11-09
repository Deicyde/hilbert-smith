---
article_id: af_a8cefed955eecb5eba0a6161
declaration: lemma
origin: background
---

# Unitary invariance on ultimate L

If $\eta:F\cong G$ is a unitary natural isomorphism of duality functors $\mathcal A\to\mathcal B$, then $F_*=G_*$ on $\mathbb L_k(\mathcal A)$.

*Proof sketch.* At level $j$, the diagonal matrices with entries $\eta_{M_n}$ have propagation $0$ and form a unitary natural isomorphism $C_{\mathbb Z^j}F\cong C_{\mathbb Z^j}G$, by induction on $j$ (naturality and unitarity hold entrywise). [Unitary invariance](../../base/groups/unitary-invariance.md) gives $(C_{\mathbb Z^j}F)_*=(C_{\mathbb Z^j}G)_*$, so $F_*\iota_j=G_*\iota_j$ by [The induced map at each level](induced-map-level.md). Every element of the colimit comes from a finite level ([Every element comes from a finite level](level-exhaustive.md)).

## Sources

- New: levelwise.

## Depends on

- [Induced map on ultimate L](induced-map.md)
- [Unitary natural isomorphism](../../base/categories/unitary-isomorphism.md)

## Proof depends on

- [Bounded extension of a duality functor](../../bounded/categories/bounded-functor.md)
- [Unitary invariance](../../base/groups/unitary-invariance.md)
- [The induced map at each level](induced-map-level.md)
- [Every element comes from a finite level](level-exhaustive.md)
