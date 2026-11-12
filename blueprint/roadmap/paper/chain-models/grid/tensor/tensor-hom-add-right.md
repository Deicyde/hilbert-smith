---
article_id: af_f28428a8fee75956bc9013c2
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.ChainModels.basedTensorHom_add_right
---

# Additivity of tensors of graded maps in the second factor

For graded maps $f_r:C_r\to C'_{r+d}$ and $g_r,g'_r:E_r\to E'_{r+e}$, where $E,E'$ vanish in negative degrees, the [tensors of graded maps](based-tensor-hom.md) satisfy $f\otimes(g+g')=f\otimes g+f\otimes g'$.

*Proof sketch.* Blockwise: the [Kronecker product is additive in its second factor](kron-add-right.md).

## Sources

- New: block calculus for the explicit bases of the chain models.

## Depends on

- [Tensor of graded maps of based complexes](based-tensor-hom.md)

## Proof depends on

- [Additivity of the Kronecker product in the second factor](kron-add-right.md)

