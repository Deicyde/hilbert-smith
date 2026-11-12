---
article_id: af_a6561b626f19fe4c54592a3b
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.ChainModels.block_ext
---

# Maps between concatenations are determined by their blocks

Two maps $F,G:\mathbb Q^{\sum_ad_a}\to\mathbb Q^{\sum_{a'}d'_{a'}}$ of [based vector spaces](../../../../l-theory/localization/products/based-vector-spaces.md) with $\pi'_qF\iota_p=\pi'_qG\iota_p$ for all blocks $p,q$ are equal. Here $\iota$ and $\pi$ (with primes) are the block inclusions and projections of the concatenations, as in the [concatenation of blocks](block-maps.md).

*Proof sketch.* Write $F=(\sum_p\iota_p\pi_p)F(\sum_q\iota'_q\pi'_q)$ by the [block decomposition of the identity](block-decomposition.md), and likewise for $G$.

## Sources

- New: block calculus for the explicit bases of the chain models.

## Depends on

- [Block inclusions and projections](block-maps.md)

## Proof depends on

- [Block decomposition of the identity](block-decomposition.md)
