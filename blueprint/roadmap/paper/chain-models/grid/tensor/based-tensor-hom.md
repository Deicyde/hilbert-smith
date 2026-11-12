---
article_id: af_9b4fe9643490a53d6060548c
declaration: def
origin: bridged
statement: formalized
lean: HSP.ChainModels.basedTensorHom
---

# Tensor of graded maps of based complexes

For graded maps $f_r:C_r\to C'_{r+d}$ and $g_r:E_r\to E'_{r+e}$, where $E$ and $E'$ vanish in negative degrees, the tensor $f\otimes g:(C\otimes E)_r\to(C'\otimes E')_{r+d+e}$ is the map whose block from $C_a\boxtimes E_{r-a}$ to $C'_{a+d}\boxtimes E'_{r-a+e}$ is $(-1)^{ea}f_a\boxtimes g_{r-a}$, when $a+d\ge0$; all other blocks, including those from $C_a\boxtimes E_{r-a}$ with $a+d<0$, are zero. Here the [tensor product of based complexes](../based-complex-tensor.md) is used on both sides, and $\boxtimes$ of matrices is the Kronecker product of the [tensor product of based vector spaces](../../../l-theory/localization/products/based-tensor.md).

## Sources

- New: explicit bases for the chain models.

## Depends on

- [Tensor product of based complexes](../based-complex-tensor.md)
- [Tensor product of based vector spaces](../../../l-theory/localization/products/based-tensor.md)
