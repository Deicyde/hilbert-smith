---
article_id: af_89449a7e461e65824325f267
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.ChainModels.basedKron_add_right
---

# Additivity of the Kronecker product in the second factor

For matrices $f:X\to X'$ and $g,g':Y\to Y'$ of [based vector spaces](../../../l-theory/localization/products/based-vector-spaces.md), the Kronecker product of the [tensor product of based vector spaces](../../../l-theory/localization/products/based-tensor.md) satisfies $f\boxtimes(g+g')=f\boxtimes g+f\boxtimes g'$.

*Proof sketch.* The Kronecker product of matrices is additive in its second factor.

## Sources

- New: block calculus for the explicit bases of the chain models.

## Depends on

- [The category of based ℚ-vector spaces](../../../l-theory/localization/products/bookkeeping/based-category.md)
- [Kronecker product of matrices](../../../l-theory/localization/products/bookkeeping/based-kron.md)
