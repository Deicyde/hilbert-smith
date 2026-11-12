---
article_id: af_78c8dec0591bb0b74d868493
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.ChainModels.chainModel_d_propagation
---

# Propagation of the differential of the chain model

For every $i$, with cells of the [chain model](../model/chain-model.md) labelled at the centers of their cubes, the differential $d$ of $D_i$ has $d_\infty$-[propagation](../../../categories/asymptotic/propagation.md) at most $h_i/2=2/k_i$.

*Proof sketch.* The [differential of a tensor product of based complexes](../tensor/tensor-differential.md) is $d\otimes1+1\otimes d$, up to transports. In the [circle complex](../cubical/circle-complex.md) $S_k$, the endpoints $[w]$ and $[w+1]$ of the edge $e_w$ lie at distance $2/k$ from its center. The cells of $P$ carry the constant label $0$, which the torus labels forget, and its differential is zero. By [the propagation bound for the tensor of graded maps](prop-product-maps.md) (3) and [the description of grid and chain-model labels as tensor labels](../model/tensor-label-grid.md), induction over the circle factors gives $2/k$ for the differential of $C(k)$, and then for $D_i=C(k_i)\otimes P$. All other components of $d$ are zero.

## Sources

- New: the explicit chain model of the cubical grid.

## Depends on

- [Chain-model labels](../model/chain-model-label.md)
- [Chain model](../model/chain-model.md)
- [Propagation](../../../categories/asymptotic/propagation.md)
- [Mesh sequence](../mesh-sequence.md)
- [Local datum](../../../local-data/chart/local-datum.md)
- [The category of based ℚ-vector spaces](../../../l-theory/localization/products/bookkeeping/based-category.md)

## Proof depends on

- [Labels of the circle cells](../cubical/circle-label.md)
- [Propagation bounds for the based product and tensor maps](prop-product-maps.md)
- [Grid and chain-model labels are tensor labels](../model/tensor-label-grid.md)
- [Labels on a tensor product of based complexes](../model/tensor-label.md)
- [Differential of a tensor product](../tensor/tensor-differential.md)
- [The identity as a map of degree zero](../tensor/id-deg0.md)
- [The circle complex](../cubical/circle-complex.md)
- [The cellular chain complex of CP^2](../cp2/cp2-complex.md)
- [Propagation of a sum](../../../categories/asymptotic/prop-add.md)
- [Propagation of a product](../../../categories/asymptotic/prop-mul.md)
- [Propagation of the identity](../../../categories/asymptotic/prop-one.md)
- [Tensor product of based complexes](../based-complex-tensor.md)
- [The cells of CP^2 vanish in negative degrees](../cp2/cp2-dim-neg.md)
- [The circle complex vanishes in negative degrees](../cubical/circle-dim-neg.md)
- [Cubical torus grid](../cubical/cubical-torus-grid.md)
- [The cube of a basis vector](../cubical/grid-cell.md)
- [The center of a grid cube](../cubical/grid-cube-center.md)
- [The torus](../torus.md)
