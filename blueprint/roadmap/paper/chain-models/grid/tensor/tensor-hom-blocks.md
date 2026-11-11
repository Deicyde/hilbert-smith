---
article_id: af_6927dcd7c2ffb177ed7129d9
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.ChainModels.blockInc_comp_basedTensorHom_comp_blockProj
---

# Blocks of a tensor of graded maps

For graded maps $f_r:C_r\to C'_{r+d}$ and $g_r:E_r\to E'_{r+e}$ ($E,E'$ vanishing in negative degrees), the block of the [tensor of graded maps](based-tensor-hom.md) $f\otimes g$ from the summand $C_p\boxtimes E_{r-p}$ of $(C\otimes E)_r$ to the summand with index $q$ of $(C'\otimes E')_{r+d+e}$ is $(-1)^{ep}f_p\boxtimes g_{r-p}$, followed by the identification of $C'_{p+d}\boxtimes E'_{r-p+e}$ with that summand, if $q=p+d$, and $0$ otherwise.

*Proof sketch.* Rewrite each summand of the definition as a block inclusion, a block and a block projection, and apply [block extraction](block-extraction.md).

## Sources

- New: block calculus for the explicit bases of the chain models.

## Depends on

- [Tensor of graded maps of based complexes](based-tensor-hom.md)

## Proof depends on

- [Block extraction](block-extraction.md)
