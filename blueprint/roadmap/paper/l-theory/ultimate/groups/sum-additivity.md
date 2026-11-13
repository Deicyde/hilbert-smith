---
article_id: af_c4b5a190314c76eeb69d5cd1
declaration: theorem
origin: background
statement: formalized
lean: HSP.ultL.map_biprod
proof: formalized
---

# Additivity on ultimate L

For duality functors $F,G:\mathcal A\to\mathcal B$, $(F\oplus G)_*=F_*+G_*$ on $\mathbb L_k(\mathcal A)$, with $F\oplus G$ their [sum](../../base/categories/sums/duality-functor-sum.md). Here the categories have objects and morphisms of the same size, as for the [induced map](induced-map.md).

*Proof sketch.* At stage $j$, [Bounded extension of a sum of functors](bounded-sum-extension.md) gives a unitary natural isomorphism $C_{\mathbb Z^j}(F\oplus G)\cong C_{\mathbb Z^j}F\oplus C_{\mathbb Z^j}G$. [Unitary invariance on L^p](../../base/groups/lp-map-unitary.md) and [Sums of functors on L^p](../../base/groups/lp-map-biprod.md) give $(C_{\mathbb Z^j}(F\oplus G))_*=(C_{\mathbb Z^j}F)_*+(C_{\mathbb Z^j}G)_*$. So $(F\oplus G)_*\iota_j=F_*\iota_j+G_*\iota_j$ by [The induced map at each stage](induced-map-level.md), since $\iota_j$ is additive. Every element of the colimit comes from a finite stage ([Every element comes from a finite stage](level-exhaustive.md)).

## Sources

- New: levelwise.

## Depends on

- [Induced map on ultimate L](induced-map.md)
- [Sum of duality functors](../../base/categories/sums/duality-functor-sum.md)
- [Small Q-linear category with strict duality](../../base/categories/duality-category.md)
- [Duality functor](../../base/categories/duality-functor.md)
- [Ultimate L-group](ultimate-l-group.md)

## Proof depends on

- [Bounded extension of a sum of functors](bounded-sum-extension.md)
- [Unitary invariance on L^p](../../base/groups/lp-map-unitary.md)
- [Sums of functors on L^p](../../base/groups/lp-map-biprod.md)
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
