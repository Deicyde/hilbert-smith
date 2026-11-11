---
article_id: af_b8360625c004403b9261ae6c
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.ChainModels.blockProj_comp_blockInc_sum
---

# Block decomposition of the identity

For a finite family of dimensions $d_1,\dots,d_m$, the identity of the concatenation $\mathbb Q^{\sum_jd_j}$ in the [based vector spaces](../../../l-theory/localization/products/based-vector-spaces.md) is $\sum_j\iota_j\pi_j$, where $\pi_j$ and $\iota_j$ are the projection onto and the inclusion of the $j$-th block, as in the [tensor product of based complexes](../based-complex-tensor.md).

*Proof sketch.* Compare entries: the entry of $\sum_j\iota_j\pi_j$ at a pair of basis vectors is $1$ exactly when both lie in the same block at the same position, that is, when they are equal.

## Sources

- New: block calculus for the explicit bases of the chain models.

## Depends on

- [Tensor product of based complexes](../based-complex-tensor.md)

## Proof depends on


