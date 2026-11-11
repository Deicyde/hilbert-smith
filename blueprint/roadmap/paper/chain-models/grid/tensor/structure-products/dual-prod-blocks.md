---
article_id: af_50bd95d14a9ce95b7e67c446
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.ChainModels.blockInc_comp_basedDualProd_comp_blockProj
---

# Blocks of a product of duality maps

For graded maps $f_r:C_r\to C^*_{m-r}$ and $g_r:E_r\to E^*_{m'-r}$, the block of the [product of duality maps](based-dual-prod.md) $\Xi^{-1}(f\otimes g)$ from the summand $C_a\boxtimes E_{r-a}$ of $(C\otimes E)_r$ to the dual of the summand with index $q$ of $(C\otimes E)_{k-r}$ is $(-1)^{(r-a)(a+m)}f_a\boxtimes g_{r-a}$ if $q=m-a$, and $0$ otherwise.

*Proof sketch.* Rewrite each summand of the definition as a block inclusion, a block and a block projection, and apply [block extraction](../block-extraction.md).

## Sources

- New: block calculus for the explicit bases of the chain models.

## Depends on

- [Product of duality maps in explicit bases](based-dual-prod.md)

## Proof depends on

- [Block extraction](../block-extraction.md)
