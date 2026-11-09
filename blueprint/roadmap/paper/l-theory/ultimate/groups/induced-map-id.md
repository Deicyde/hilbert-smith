---
article_id: af_9ae6446f2e3e152e8b884d20
declaration: lemma
origin: background
---

# Identity on ultimate L

$(\mathrm{id}_{\mathcal A})_*=\mathrm{id}$ on $\mathbb L_k(\mathcal A)$.

*Proof sketch.* By induction on $j$, $C_{\mathbb Z^j}(\mathrm{id}_{\mathcal A})$ is the identity functor of $C_{\mathbb Z^j}\mathcal A$, since bounded extension applies the functor entrywise. At level $j$, [Identity induces the identity](../../base/groups/induced-map-id.md) and [The induced map at each level](induced-map-level.md) give $(\mathrm{id})_*\iota_j=\iota_j$. Every element of the colimit comes from a finite level ([Every element comes from a finite level](level-exhaustive.md)).

## Sources

- New: levelwise.

## Depends on

- [Induced map on ultimate L](induced-map.md)

## Proof depends on

- [Bounded extension of a duality functor](../../bounded/categories/bounded-functor.md)
- [Identity induces the identity](../../base/groups/induced-map-id.md)
- [The induced map at each level](induced-map-level.md)
- [Every element comes from a finite level](level-exhaustive.md)
