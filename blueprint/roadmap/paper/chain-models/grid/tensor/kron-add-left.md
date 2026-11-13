---
article_id: af_087a8f9f6c6175d1351c1e5a
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.ChainModels.basedKron_add_left
---

# Additivity of the Kronecker product in the first factor

For matrices $f,f':X\to X'$ and $g:Y\to Y'$ of [based vector spaces](../../../l-theory/localization/products/based-vector-spaces.md), the Kronecker product of the [tensor product of based vector spaces](../../../l-theory/localization/products/based-tensor.md) satisfies $(f+f')\boxtimes g=f\boxtimes g+f'\boxtimes g$.

*Proof sketch.* The Kronecker product of matrices is additive in its first factor.

## Sources

- New: block calculus for the explicit bases of the chain models.

## Depends on

- [The category of based ℚ-vector spaces](../../../l-theory/localization/products/bookkeeping/based-category.md)
- [Kronecker product of matrices](../../../l-theory/localization/products/bookkeeping/based-kron.md)
