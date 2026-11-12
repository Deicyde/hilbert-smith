---
article_id: af_9a9c7c80ca818ba28da485b3
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.ChainModels.blockInc_comp_basedStrProd_comp_blockProj
---

# Blocks of a product of structures

For $\varphi\in M(C)_m$ and $\theta\in M(E)_{m'}$, the block of the [product of structures](based-str-prod.md) $(\varphi\otimes\theta)_{r,s}$ from the dual of the summand with index $a$ of $(C\otimes E)_s$ to the summand $C_p\boxtimes E_{r-p}$ of $(C\otimes E)_r$ is $(-1)^{(r-p)(p+m)}\varphi_p\boxtimes\theta_{r-p}$ (after identifying the dual summand with $C_{m-p}^*\boxtimes E_{m'-r+p}^*$) if $a=m-p$, and $0$ otherwise.

*Proof sketch.* Rewrite each summand of the definition as a block inclusion, a block and a block projection, and apply [block extraction](../block-extraction.md).

## Sources

- New: block calculus for the explicit bases of the chain models.

## Depends on

- [Product of structures in explicit bases](based-str-prod.md)

## Proof depends on

- [Block extraction](../block-extraction.md)
