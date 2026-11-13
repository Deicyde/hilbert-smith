---
article_id: af_eee14495b390b41663425947
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.ChainModels.basedTensorHom_id
---

# Tensor of identities

Let $C$ and $E$ be complexes of based vector spaces, $E$ vanishing in negative degrees. The [tensor](based-tensor-hom.md) of the [identities of degree zero](id-deg0.md) of $C$ and $E$ is the identity of $C\otimes E$: $1_C\otimes1_E=1_{C\otimes E}$.

*Proof sketch.* The block of $1_C\otimes1_E$ from the summand $p$ to the summand $p$ is the Kronecker product of identities, which is the identity ([Kronecker product of identities](kron-transport.md)); all other blocks vanish. The identity is the sum of its diagonal blocks ([block decomposition of the identity](blocks/block-decomposition.md)).

## Sources

- New: block calculus for the explicit bases of the chain models.

## Depends on

- [Tensor of graded maps of based complexes](based-tensor-hom.md)
- [The identity as a map of degree zero](id-deg0.md)
- [Tensor product of based complexes](../based-complex-tensor.md)
- [The category of based ℚ-vector spaces](../../../l-theory/localization/products/bookkeeping/based-category.md)

## Proof depends on

- [Kronecker product of identities](kron-transport.md)
- [Block decomposition of the identity](blocks/block-decomposition.md)
- [Block inclusions and projections](blocks/block-maps.md)
- [Kronecker product of matrices](../../../l-theory/localization/products/bookkeeping/based-kron.md)
