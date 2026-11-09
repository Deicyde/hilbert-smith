---
article_id: af_fd90944952160480a557a0ae
declaration: lemma
origin: background
---

# Functoriality on ultimate L

For duality functors $F:\mathcal A\to\mathcal B$ and $G:\mathcal B\to\mathcal C$, $(G\circ F)_*=G_*\circ F_*$ on $\mathbb L_k$.

*Proof sketch.* By induction on $j$, $C_{\mathbb Z^j}(GF)=C_{\mathbb Z^j}G\circ C_{\mathbb Z^j}F$, using $C_{\mathbb Z}(GF)=C_{\mathbb Z}(G)C_{\mathbb Z}(F)$ at each step. So at level $j$ the two sides agree by [Functoriality of induced maps](../../base/groups/induced-map-comp.md) and [The induced map at each level](induced-map-level.md). Every element of the colimit comes from a finite level ([Every element comes from a finite level](level-exhaustive.md)).

## Sources

- New: levelwise.

## Depends on

- [Induced map on ultimate L](induced-map.md)

## Proof depends on

- [Bounded extension of a duality functor](../../bounded/categories/bounded-functor.md)
- [Functoriality of induced maps](../../base/groups/induced-map-comp.md)
- [The induced map at each level](induced-map-level.md)
- [Every element comes from a finite level](level-exhaustive.md)
