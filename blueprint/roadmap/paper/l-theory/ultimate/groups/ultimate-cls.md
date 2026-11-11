---
article_id: af_2ce0ad9555b6da7428f06411
declaration: def
origin: background
statement: formalized
lean: HSP.cls
---

# The class map

$\mathrm{cls}:L^p_k(\mathcal A)\to\mathbb L_k(\mathcal A)$ is the [stage map](ultimate-stage-map.md) $\iota_0$, under $L^p_k(\mathcal A)=L^{\langle 0\rangle}_k(\mathcal A)$ ([Lower L-group](../../localization/transitions/lower-l-group.md)).

*Notation.* For a strict symmetric Poincaré complex $(C,\phi)$ in $\mathcal A$ itself, $\mathrm{cls}(C,\phi)$ abbreviates $\mathrm{cls}[\mathrm{emb}_{\mathcal A}C,\phi]=\mathrm{cls}[(C,1),\phi]$, the class of its [image](../../base/pairs/functor-poincare.md) under the strict duality functor $\mathrm{emb}_{\mathcal A}:\mathcal A\to\mathrm{Kar}\,\mathcal A$, the [Karoubi embedding](../../base/categories/karoubi-embedding.md): chain objects $(C_r,1)$, with the same differentials and structure maps.

(Lean: $L^{\langle 0\rangle}_k(\mathcal A)=L^p_{k+0}(\mathcal A)$, so $\mathrm{cls}$ is $\iota_0$ precomposed with the transport $L^p_k(\mathcal A)\cong L^p_{k+0}(\mathcal A)$ of L-groups along the equality of degrees $k=k+0$. The notation $\mathrm{cls}(C,\phi)$ has no declaration of its own.)

## Sources

- [Carlsson-Pedersen 1995, Def 4.16](../../../../../sources/paper/carlsson-pedersen-1995.md) [U]

## Depends on

- [Stage maps into the ultimate L-group](ultimate-stage-map.md)
- [Lower L-group](../../localization/transitions/lower-l-group.md)
- [Embedding into the idempotent completion](../../base/categories/karoubi-embedding.md)
- [Duality functors carry Poincaré complexes](../../base/pairs/functor-poincare.md)
