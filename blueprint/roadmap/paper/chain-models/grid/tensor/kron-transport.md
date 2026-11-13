---
article_id: af_376a1acf8bc69e7cb4f466d4
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.ChainModels.basedKron_eqToHom
---

# Kronecker product of identities

If $X=X'$ and $Y=Y'$ are equal [based vector spaces](../../../l-theory/localization/products/based-vector-spaces.md), the Kronecker product of the [tensor product of based vector spaces](../../../l-theory/localization/products/based-tensor.md) of the two identifications is the identification of $X\boxtimes Y$ with $X'\boxtimes Y'$; in particular $1\boxtimes1=1$.

*Proof sketch.* After identifying, this is $1\otimes_k1=1$ for Kronecker products, reindexed.

## Sources

- New: block calculus for the explicit bases of the chain models.

## Depends on

- [The category of based ℚ-vector spaces](../../../l-theory/localization/products/bookkeeping/based-category.md)
- [Kronecker product of matrices](../../../l-theory/localization/products/bookkeeping/based-kron.md)
