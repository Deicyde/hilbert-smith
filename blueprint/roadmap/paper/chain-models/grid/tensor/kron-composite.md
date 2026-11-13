---
article_id: af_e4bdb4fedcded1b273eaf4ed
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.ChainModels.basedKron_comp_basedKron
---

# Kronecker product of composites

For matrices $f:X\to X'$, $f':X'\to X''$, $g:Y\to Y'$, $g':Y'\to Y''$ of [based vector spaces](../../../l-theory/localization/products/based-vector-spaces.md), the Kronecker products of the [tensor product of based vector spaces](../../../l-theory/localization/products/based-tensor.md) satisfy $(f'\boxtimes g')(f\boxtimes g)=(f'f)\boxtimes(g'g)$.

*Proof sketch.* The mixed-product rule for Kronecker products, reindexed along the same bijection on both sides.

## Sources

- New: block calculus for the explicit bases of the chain models.

## Depends on

- [The category of based ℚ-vector spaces](../../../l-theory/localization/products/bookkeeping/based-category.md)
- [Kronecker product of matrices](../../../l-theory/localization/products/bookkeeping/based-kron.md)
