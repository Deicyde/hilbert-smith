---
article_id: af_1d6e5c8875e800fea3216882
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.ChainModels.blockInc_comp_basedTensorHom_comp_eqToHom_comp_blockProj
---

# Blocks of a transported tensor of graded maps

For graded maps $f_r:C_r\to C'_{r+d}$ and $g_r:E_r\to E'_{r+e}$ ($E,E'$ vanishing in negative degrees) and $s=r+d+e$, the block of the [tensor of graded maps](../based-tensor-hom.md) $f\otimes g$, followed by the identification of $(C'\otimes E')_{r+d+e}$ with $(C'\otimes E')_s$, from the summand $C_p\boxtimes E_{r-p}$ to the summand with index $q$ of $(C'\otimes E')_s$ is $(-1)^{ep}f_p\boxtimes g_{r-p}$ if $q=p+d$, and $0$ otherwise.

*Proof sketch.* This is the [blocks of a tensor of graded maps](../tensor-hom-blocks.md) after the identity transport.

## Sources

- New: block calculus for the explicit bases of the chain models.

## Depends on

- [Tensor of graded maps of based complexes](../based-tensor-hom.md)

## Proof depends on

- [Blocks of a tensor of graded maps](../tensor-hom-blocks.md)
