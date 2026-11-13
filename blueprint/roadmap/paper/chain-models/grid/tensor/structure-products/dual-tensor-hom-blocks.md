---
article_id: af_192e0ee3455d08aa779f1f41
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.ChainModels.blockInc_comp_basedDualTensorHom_comp_eqToHom_comp_blockProj
---

# Blocks of a dual tensor of graded maps

For maps $F$ of $C^{m-*}$ of degree $d$ and $G$ of $E^{m'-*}$ of degree $e$ ($E$ vanishing in negative degrees, $m+m'=k$, $s=r+d+e$), the block of the [dual tensor of graded maps](../based-dual-tensor-hom.md) $\Xi^{-1}(F\otimes G)\Xi$, followed by the identification of $(C\otimes E)^{k-*}_{r+d+e}$ with $(C\otimes E)^{k-*}_s$, from the dual of the summand $p$ of $(C\otimes E)_{k-r}$ to the dual of the summand $q$ of $(C\otimes E)_{k-s}$ is $\pm F_{m-p}\boxtimes G_{r-m+p}$ if $q=p-d$, with the sign $(-1)^{(r-m+p+e)(2m-p+d)+e(m-p)+(r-m+p)(2m-p)}$, and $0$ otherwise.

*Proof sketch.* Rewrite each summand of the definition as a block inclusion, a block and a block projection, and apply [block extraction](../blocks/block-extraction.md).

## Sources

- New: block calculus for the explicit bases of the chain models.

## Depends on

- [Dual tensor of graded maps of based complexes](../based-dual-tensor-hom.md)
- [Tensor product of based complexes](../../based-complex-tensor.md)
- [Block inclusions and projections](../blocks/block-maps.md)
- [Small Q-linear category with strict duality](../../../../l-theory/base/categories/duality-category.md)
- [Based vector spaces](../../../../l-theory/localization/products/based-vector-spaces.md)
- [The category of based ℚ-vector spaces](../../../../l-theory/localization/products/bookkeeping/based-category.md)
- [Kronecker product of matrices](../../../../l-theory/localization/products/bookkeeping/based-kron.md)

## Proof depends on

- [Block extraction](../blocks/block-extraction.md)
