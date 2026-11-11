---
article_id: af_0c6cf8662dd8330bd76f6a42
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.ChainModels.basedComplexTensor_d_eq
---

# Differential of a tensor product

Let $C$ and $E$ be complexes of based vector spaces, $E$ vanishing in negative degrees. The differential of the [tensor product](../based-complex-tensor.md) is
$$d_{C\otimes E}=d_C\otimes1_E+1_C\otimes d_E,$$
a sum of [tensors of graded maps](based-tensor-hom.md), where $d_C$ and $d_E$ have degree $-1$ and $1_C$, $1_E$ are the [identities of degree zero](id-deg0.md). By the sign rule this is $d\boxtimes1+(-1)^p\,1\boxtimes d$ on $C_p\boxtimes E_{r-p}$.

*Proof sketch.* Compare blocks ([maps are determined by their blocks](block-ext.md)). The block of the differential from the summand $p$ of degree $r$ to the summand $q$ of degree $r-1$ is $d\boxtimes1$ if $q=p-1$, $(-1)^p\,1\boxtimes d$ if $q=p$, and $0$ otherwise ([block extraction](block-extraction.md)). By the [blocks of a transported tensor of graded maps](structure-products/tensor-hom-transport-blocks.md), $d_C\otimes1_E$ contributes $d\boxtimes1$ exactly when $q=p-1$, with sign $(-1)^{0\cdot p}=1$, and $1_C\otimes d_E$ contributes $(-1)^{-p}\,1\boxtimes d$ exactly when $q=p$.

## Sources

- New: block calculus for the explicit bases of the chain models.

## Depends on

- [Tensor product of based complexes](../based-complex-tensor.md)
- [Tensor of graded maps of based complexes](based-tensor-hom.md)
- [The identity as a map of degree zero](id-deg0.md)

## Proof depends on

- [Maps between concatenations are determined by their blocks](block-ext.md)
- [Block extraction](block-extraction.md)
- [Blocks of a transported tensor of graded maps](structure-products/tensor-hom-transport-blocks.md)
