---
article_id: af_e49009894c1f9e9900440fe3
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.ChainModels.block_comp
---

# Blocks of a composite

For maps $F:\mathbb Q^{\sum_ad_a}\to\mathbb Q^{\sum_{a'}d'_{a'}}$ and $G:\mathbb Q^{\sum_{a'}d'_{a'}}\to\mathbb Q^{\sum_{a''}d''_{a''}}$ of [based vector spaces](../../../l-theory/localization/products/based-vector-spaces.md), $\pi''_q(GF)\iota_p=\sum_{a'}(\pi''_qG\iota'_{a'})(\pi'_{a'}F\iota_p)$.

*Proof sketch.* Insert the [block decomposition of the identity](block-decomposition.md) between $F$ and $G$.

## Sources

- New: block calculus for the explicit bases of the chain models.

## Depends on

- [Tensor product of based complexes](../based-complex-tensor.md)

## Proof depends on

- [Block decomposition of the identity](block-decomposition.md)
