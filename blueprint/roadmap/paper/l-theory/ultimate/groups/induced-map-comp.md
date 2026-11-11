---
article_id: af_fd90944952160480a557a0ae
declaration: lemma
origin: background
---

# Functoriality on ultimate L

For duality functors $F:\mathcal A\to\mathcal B$ and $G:\mathcal B\to\mathcal C$, $(G\circ F)_*=G_*\circ F_*$ on $\mathbb L_k$.

*Proof sketch.* $C_{\mathbb Z^j}(GF)=C_{\mathbb Z^j}G\circ C_{\mathbb Z^j}F$ as duality functors by [Bounded extension is functorial](../../bounded/categories/bounded-functor-comp.md). So at stage $j$ the two sides agree by [Functoriality on L^p](../../base/groups/lp-functoriality.md), item 1, and [The induced map at each stage](induced-map-level.md). Every element of the colimit comes from a finite stage ([Every element comes from a finite stage](level-exhaustive.md)).

## Sources

- New: levelwise.

## Depends on

- [Induced map on ultimate L](induced-map.md)

## Proof depends on

- [Bounded extension is functorial](../../bounded/categories/bounded-functor-comp.md)
- [Functoriality on L^p](../../base/groups/lp-functoriality.md)
- [The induced map at each stage](induced-map-level.md)
- [Every element comes from a finite stage](level-exhaustive.md)
