---
article_id: af_ba868550b483f7e6398d11a9
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.ChainModels.basedStrProd_zero_right
---

# A product of structures with a zero right factor

Let $C$ and $E$ be complexes of based vector spaces, $E$ vanishing in negative degrees. The [product of structures](based-str-prod.md) $\varphi\otimes0$ of any $\varphi\in M(C)_m$ with the zero structure of $E$ is $0$.

*Proof sketch.* Every block of $\varphi\otimes0$ is, up to sign and transport, a Kronecker product with the zero factor $0$ ([Kronecker product with a zero factor](../kron-zero.md)).

## Sources

- New: block calculus for the explicit bases of the chain models.

## Depends on

- [Product of structures in explicit bases](based-str-prod.md)
- [Tensor product of based complexes](../../based-complex-tensor.md)
- [Small Q-linear category with strict duality](../../../../l-theory/base/categories/duality-category.md)
- [Structure complex](../../../../l-theory/base/complexes/structure-complex.md)
- [Based vector spaces](../../../../l-theory/localization/products/based-vector-spaces.md)
- [The category of based ℚ-vector spaces](../../../../l-theory/localization/products/bookkeeping/based-category.md)

## Proof depends on

- [Kronecker product with a zero factor](../kron-zero.md)
- [Block inclusions and projections](../blocks/block-maps.md)
- [Kronecker product of matrices](../../../../l-theory/localization/products/bookkeeping/based-kron.md)
