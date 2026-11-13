---
article_id: af_e512ca9fe5858651f3910994
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.ChainModels.prop_productMaps
---

# Propagation bounds for the based product and tensor maps

Label the basis of $C\otimes E$ by [tensor labels](../model/tensor-label.md) combined by a map that is $1$-Lipschitz for the max distance. Suppose the graded maps on $C$ have [propagation](../../../categories/asymptotic/propagation.md) at most $\varepsilon_C$ and those on $E$ at most $\varepsilon_E$. Then each of the following has propagation at most $\max(\varepsilon_C,\varepsilon_E)$:

1. the [product of structures](../tensor/structure-products/based-str-prod.md);
2. the [product of duality maps](../tensor/structure-products/based-dual-prod.md);
3. the [tensor](../tensor/based-tensor-hom.md) of graded maps;
4. the [dual tensor](../tensor/based-dual-tensor-hom.md) of graded maps.

*Proof sketch.* Up to sign, every summand in the definitions of these maps is a block projection, transports, a Kronecker product of factor blocks and a block inclusion. Block projections, inclusions and transports have propagation $0$ ([propagation of the identity](../../../categories/asymptotic/prop-one.md)). A Kronecker product has propagation at most the larger of its factors', because the combining map is $1$-Lipschitz. Composites, signs and sums are bounded by [propagation of a product](../../../categories/asymptotic/prop-mul.md), [of a scalar multiple](../../../categories/asymptotic/prop-smul.md) and [of a sum](../../../categories/asymptotic/prop-add.md).

## Sources

- New: the explicit chain model of the cubical grid.

## Depends on

- [Labels on a tensor product of based complexes](../model/tensor-label.md)
- [Propagation](../../../categories/asymptotic/propagation.md)
- [Product of structures in explicit bases](../tensor/structure-products/based-str-prod.md)
- [Product of duality maps in explicit bases](../tensor/structure-products/based-dual-prod.md)
- [Tensor of graded maps of based complexes](../tensor/based-tensor-hom.md)
- [Dual tensor of graded maps of based complexes](../tensor/based-dual-tensor-hom.md)
- [Small Q-linear category with strict duality](../../../l-theory/base/categories/duality-category.md)
- [Structure complex](../../../l-theory/base/complexes/structure-complex.md)
- [The category of based ℚ-vector spaces](../../../l-theory/localization/products/bookkeeping/based-category.md)
- [Tensor product of based complexes](../based-complex-tensor.md)
- [Based vector spaces](../../../l-theory/localization/products/based-vector-spaces.md)

## Proof depends on

- [Propagation of the identity](../../../categories/asymptotic/prop-one.md)
- [Propagation of a product](../../../categories/asymptotic/prop-mul.md)
- [Propagation of a scalar multiple](../../../categories/asymptotic/prop-smul.md)
- [Propagation of a sum](../../../categories/asymptotic/prop-add.md)
- [Kronecker product of matrices](../../../l-theory/localization/products/bookkeeping/based-kron.md)
- [Block inclusions and projections](../tensor/blocks/block-maps.md)
