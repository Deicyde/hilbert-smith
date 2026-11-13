---
article_id: af_fd90944952160480a557a0ae
declaration: theorem
origin: background
statement: formalized
lean: HSP.ultL.map_comp
proof: formalized
---

# Functoriality on ultimate L

For duality functors $F:\mathcal A\to\mathcal B$ and $G:\mathcal B\to\mathcal C$, $(G\circ F)_*=G_*\circ F_*$ on $\mathbb L_k$. Here the categories have objects and morphisms of the same size, as for the [induced map](induced-map.md).

*Proof sketch.* $C_{\mathbb Z^j}(GF)=C_{\mathbb Z^j}G\circ C_{\mathbb Z^j}F$ as duality functors by [Bounded extension is functorial](../../bounded/categories/bounded-functor-comp.md). So at stage $j$ the two sides agree by [Composites on L^p](../../base/groups/lp-map-comp.md) and [The induced map at each stage](induced-map-level.md). Every element of the colimit comes from a finite stage ([Every element comes from a finite stage](level-exhaustive.md)).

## Sources

- New: levelwise.

## Depends on

- [Induced map on ultimate L](induced-map.md)
- [Small Q-linear category with strict duality](../../base/categories/duality-category.md)
- [Duality functor](../../base/categories/duality-functor.md)
- [Identity and composite duality functors](../../base/categories/duality-functors/composite-duality-functor.md)
- [Ultimate L-group](ultimate-l-group.md)

## Proof depends on

- [Bounded extension is functorial](../../bounded/categories/bounded-functor-comp.md)
- [Composites on L^p](../../base/groups/lp-map-comp.md)
- [The induced map at each stage](induced-map-level.md)
- [Every element comes from a finite stage](level-exhaustive.md)
- [Idempotent completion with duality](../../base/categories/karoubi-duality.md)
- [Induced homomorphism](../../base/groups/induced-map.md)
- [Group structure on L](../../base/groups/l-group-add.md)
- [The projective L-group](../../base/groups/projective-l-group.md)
- [Iterated bounded extension](../../bounded/categories/bounded-functor-iter.md)
- [Iterated bounded categories](../../bounded/categories/iterated-bounded-category.md)
- [Lower L-group](../../localization/transitions/lower-l-group.md)
- [Stage maps into the ultimate L-group](ultimate-stage-map.md)
