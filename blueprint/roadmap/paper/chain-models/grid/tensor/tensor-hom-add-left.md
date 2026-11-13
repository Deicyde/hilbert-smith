---
article_id: af_3db1096f02b7823a8c4af7e8
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.ChainModels.basedTensorHom_add_left
---

# Additivity of tensors of graded maps in the first factor

For graded maps $f_r,f'_r:C_r\to C'_{r+d}$ and $g_r:E_r\to E'_{r+e}$, where $E,E'$ vanish in negative degrees, the [tensors of graded maps](based-tensor-hom.md) satisfy $(f+f')\otimes g=f\otimes g+f'\otimes g$.

*Proof sketch.* Blockwise: the [Kronecker product is additive in its first factor](kron-add-left.md).

## Sources

- New: block calculus for the explicit bases of the chain models.

## Depends on

- [Tensor of graded maps of based complexes](based-tensor-hom.md)
- [Tensor product of based complexes](../based-complex-tensor.md)
- [The category of based ℚ-vector spaces](../../../l-theory/localization/products/bookkeeping/based-category.md)

## Proof depends on

- [Additivity of the Kronecker product in the first factor](kron-add-left.md)
- [Block inclusions and projections](blocks/block-maps.md)
- [Kronecker product of matrices](../../../l-theory/localization/products/bookkeeping/based-kron.md)
