---
article_id: af_073be1cff4acd020446f4d47
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.ChainModels.blockInc_comp_blockSum_comp_blockProj
---

# Block extraction

For concatenations $\mathbb Q^{\sum_ad_a}$ and $\mathbb Q^{\sum_{a'}d'_{a'}}$ of [based vector spaces](../../../../l-theory/localization/products/based-vector-spaces.md) and matrices $X_{a,a'}:\mathbb Q^{d_a}\to\mathbb Q^{d'_{a'}}$, the map $\sum_{a,a'}\iota'_{a'}X_{a,a'}\pi_a$ satisfies $\pi'_q\bigl(\sum_{a,a'}\iota'_{a'}X_{a,a'}\pi_a\bigr)\iota_p=X_{p,q}$, with the block projections $\pi$ and inclusions $\iota$ of the [concatenation of blocks](block-maps.md).

*Proof sketch.* Expand and use $\pi_{p'}\iota_p=\delta_{pp'}$ on both sides.

## Sources

- New: block calculus for the explicit bases of the chain models.

## Depends on

- [Block inclusions and projections](block-maps.md)
- [The category of based ℚ-vector spaces](../../../../l-theory/localization/products/bookkeeping/based-category.md)

## Proof depends on

- [Block projections of the inclusions](block-projections.md)
