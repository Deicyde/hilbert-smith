---
article_id: af_a8cefed955eecb5eba0a6161
declaration: theorem
origin: background
statement: formalized
lean: HSP.ultL.map_eq_of_unitaryIso
proof: formalized
---

# Unitary invariance on ultimate L

If $\eta:F\cong G$ is a unitary natural isomorphism of duality functors $\mathcal A\to\mathcal B$, then $F_*=G_*$ on $\mathbb L_k(\mathcal A)$. Here the categories have objects and morphisms of the same size, as for the [induced map](induced-map.md).

*Proof sketch.* At stage $j$, [Bounded extension of a unitary isomorphism](bounded-unitary-extension.md) gives a unitary natural isomorphism $C_{\mathbb Z^j}\eta:C_{\mathbb Z^j}F\cong C_{\mathbb Z^j}G$. [Unitary invariance on L^p](../../base/groups/lp-map-unitary.md) gives $(C_{\mathbb Z^j}F)_*=(C_{\mathbb Z^j}G)_*$, so $F_*\iota_j=G_*\iota_j$ by [The induced map at each stage](induced-map-level.md). Every element of the colimit comes from a finite stage ([Every element comes from a finite stage](level-exhaustive.md)).

## Sources

- New: levelwise.

## Depends on

- [Induced map on ultimate L](induced-map.md)
- [Unitary natural isomorphism](../../base/categories/unitary-isomorphism.md)
- [Small Q-linear category with strict duality](../../base/categories/duality-category.md)
- [Duality functor](../../base/categories/duality-functor.md)
- [Ultimate L-group](ultimate-l-group.md)

## Proof depends on

- [Bounded extension of a unitary isomorphism](bounded-unitary-extension.md)
- [Unitary invariance on L^p](../../base/groups/lp-map-unitary.md)
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
