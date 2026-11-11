---
article_id: af_9396dafecc6f9bc4d2599d25
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.ChainModels.chainModel_poincare_propagation
---

# The chain model is Poincaré: propagation

For every $i$, with cells and duals of the [chain model](../model/chain-model.md) labelled at their centers, the structure $\varphi_i$ and the map $b_i$ of [chain-model duality](../chain-model-duality.md), the [homotopy](chain-model-h.md) $H_i$ and the [dual homotopy](chain-model-h-dual.md) $H'_i$ have $d_\infty$-[propagation](../../../categories/asymptotic/propagation.md) at most $h_i=4/k_i$.

*Proof sketch.* By [the propagation bounds for the based product and tensor maps](prop-product-maps.md), the product of structures, the product of duality maps, the tensor and the dual tensor have propagation at most the larger of the bounds for their factors, for labels combined by a $1$-Lipschitz map. [Grid and chain-model labels are such tensor labels](../model/tensor-label-grid.md): on the grid the centers of the [cubes](../cubical/grid-cell.md) combine the [labels of the circle cells](../cubical/circle-label.md) by appending a coordinate, and the [chain-model labels](../model/chain-model-label.md) forget the $\mathbb{CP}^2$ factor, whose maps then count with propagation $0$. Transports have propagation $0$ ([propagation of the identity](../../../categories/asymptotic/prop-one.md)); sums and composites are bounded by [propagation of a sum](../../../categories/asymptotic/prop-add.md) and [of a product](../../../categories/asymptotic/prop-mul.md). By induction over the circle factors, with $\varphi^s$, $b$, $K$, $K'$ of propagation at most $2/k_i$ ([circle duality](../circle-duality.md) (5)), the [grid structure](../model/grid-structure.md) and the [grid duality map](grid-factor/grid-dual-map.md) have propagation at most $2/k_i$, and the [grid homotopy](grid-factor/grid-h.md) and the [dual grid homotopy](grid-factor/grid-h-dual.md) at most $4/k_i$, through [$A=\varphi^sb$](grid-factor/circle-a.md) and [$A'=b\varphi^s$](grid-factor/circle-a-dual.md).

## Sources

- New: the explicit chain model of the cubical grid.

## Depends on

- [Torus labels of chain-model cells](../model/chain-model-label.md)
- [Chain model](../model/chain-model.md)
- [Chain-model duality](../chain-model-duality.md)
- [The homotopy of the chain model](chain-model-h.md)
- [The dual homotopy of the chain model](chain-model-h-dual.md)
- [Propagation](../../../categories/asymptotic/propagation.md)

## Proof depends on

- [Propagation bounds for the based product and tensor maps](prop-product-maps.md)
- [Grid and chain-model labels are tensor labels](../model/tensor-label-grid.md)
- [Labels on a tensor product of based complexes](../model/tensor-label.md)
- [Propagation of a sum](../../../categories/asymptotic/prop-add.md)
- [Propagation of a product](../../../categories/asymptotic/prop-mul.md)
- [Propagation of the identity](../../../categories/asymptotic/prop-one.md)
- [Circle duality](../circle-duality.md)
- [Labels of the circle cells](../cubical/circle-label.md)
- [Torus labels of chain-model cells](../model/chain-model-label.md)
- [The cube of a basis vector](../cubical/grid-cell.md)
- [The center of a grid cube](../cubical/grid-cube-center.md)
- [The structure of the grid complex](../model/grid-structure.md)
- [The iterated grid duality map](grid-factor/grid-dual-map.md)
- [The grid homotopy](grid-factor/grid-h.md)
- [The dual grid homotopy](grid-factor/grid-h-dual.md)
- [The degree-zero map A of the circle](grid-factor/circle-a.md)
- [The degree-zero map A' of the dual circle](grid-factor/circle-a-dual.md)
- [The identity of a dual complex as a map of degree zero](grid-factor/id-dual-deg0.md)
- [The identity as a map of degree zero](../tensor/id-deg0.md)
- [The cells of CP^2 vanish in negative degrees](../cp2/cp2-dim-neg.md)
- [The circle complex vanishes in negative degrees](../cubical/circle-dim-neg.md)
