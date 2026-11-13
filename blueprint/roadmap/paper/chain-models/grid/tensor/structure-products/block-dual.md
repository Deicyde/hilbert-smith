---
article_id: af_091fc6f467bb963c85aa0cef
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.ChainModels.blockInc_comp_dualHom_comp_blockProj
---

# Blocks of a transpose

Let $X:\mathbb Q^{\sum_ad_a}\to\mathbb Q^{\sum_{a'}d'_{a'}}$ be a map of [based vector spaces](../../../../l-theory/localization/products/based-vector-spaces.md), whose dual is the transpose. With the block inclusions $\iota$ and projections $\pi$ of the [tensor product of based complexes](../../based-complex-tensor.md), $\pi_pX^*\iota'_q=(\pi'_qX\iota_p)^*$: the blocks of $X^*$ are the transposes of the blocks of $X$.

*Proof sketch.* The transpose of a block inclusion is the block projection, and the dual reverses composition.

## Sources

- New: block calculus for the explicit bases of the chain models.

## Depends on

- [Based vector spaces](../../../../l-theory/localization/products/based-vector-spaces.md)
- [Block inclusions and projections](../blocks/block-maps.md)
- [Small Q-linear category with strict duality](../../../../l-theory/base/categories/duality-category.md)
- [The category of based ℚ-vector spaces](../../../../l-theory/localization/products/bookkeeping/based-category.md)
