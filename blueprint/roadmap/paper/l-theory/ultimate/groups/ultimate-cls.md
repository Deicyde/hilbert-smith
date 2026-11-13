---
article_id: af_2ce0ad9555b6da7428f06411
declaration: def
origin: background
statement: formalized
lean: HSP.cls
---

# The class map

$\mathrm{cls}:L^p_k(\mathcal A)\to\mathbb L_k(\mathcal A)$ is the [stage map](ultimate-stage-map.md) $\iota_0$, under $L^p_k(\mathcal A)=L^{\langle 0\rangle}_k(\mathcal A)$ ([Lower L-group](../../localization/transitions/lower-l-group.md)).

*Notation.* For a strict symmetric Poincaré complex $(C,\phi)$ in $\mathcal A$ itself, $\mathrm{cls}(C,\phi)$ abbreviates $\mathrm{cls}[\mathrm{emb}_{\mathcal A}C,\phi]=\mathrm{cls}[(C,1),\phi]$, the class of its image under the [Karoubi embedding](../../base/categories/karoubi-embedding.md) $\mathrm{emb}_{\mathcal A}:\mathcal A\to\mathrm{Kar}\,\mathcal A$, a [strict](../../base/categories/duality-functors/karoubi-embedding-strict.md) duality functor: chain objects $(C_r,1)$, with the same differentials and structure maps.

Here $L^{\langle 0\rangle}_k(\mathcal A)=L^p_{k+0}(C_{\mathbb Z^0}\mathcal A)$, so $\mathrm{cls}$ is $\iota_0$ precomposed with the [transport of L-groups](../../base/groups/l-group-cast.md) along $k=k+0$.

## Sources

- [Carlsson-Pedersen 1995, Def 4.16](../../../../../sources/paper/carlsson-pedersen-1995.md) [U]

## Depends on

- [The projective L-group](../../base/groups/projective-l-group.md)
- [Small Q-linear category with strict duality](../../base/categories/duality-category.md)
- [Idempotent completion with duality](../../base/categories/karoubi-duality.md)
- [Group structure on L](../../base/groups/l-group-add.md)
- [Ultimate L-group](ultimate-l-group.md)

## Proof depends on

- [Transport of L-groups along an equality of degrees](../../base/groups/l-group-cast.md)
- [L-group](../../base/groups/l-group.md)
- [Iterated bounded categories](../../bounded/categories/iterated-bounded-category.md)
- [Lower L-group](../../localization/transitions/lower-l-group.md)
- [Stage maps into the ultimate L-group](ultimate-stage-map.md)
