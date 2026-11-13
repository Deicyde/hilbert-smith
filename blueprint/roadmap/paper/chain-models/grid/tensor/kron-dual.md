---
article_id: af_7d5836f88d5baeed04fd656f
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.ChainModels.dualHom_basedKron
---

# Transpose of a Kronecker product

For matrices $f:X\to X'$ and $g:Y\to Y'$ of [based vector spaces](../../../l-theory/localization/products/based-vector-spaces.md), whose duals are the transposes, the [Kronecker product](../../../l-theory/localization/products/bookkeeping/based-kron.md) satisfies $(f\boxtimes g)^*=f^*\boxtimes g^*$.

*Proof sketch.* The transpose of a Kronecker product of matrices is the Kronecker product of the transposes, and the reindexing by Kronecker positions commutes with transposition.

## Sources

- New: block calculus for the explicit bases of the chain models.

## Depends on

- [Based vector spaces](../../../l-theory/localization/products/based-vector-spaces.md)
- [Small Q-linear category with strict duality](../../../l-theory/base/categories/duality-category.md)
- [The category of based ℚ-vector spaces](../../../l-theory/localization/products/bookkeeping/based-category.md)
- [Kronecker product of matrices](../../../l-theory/localization/products/bookkeeping/based-kron.md)
