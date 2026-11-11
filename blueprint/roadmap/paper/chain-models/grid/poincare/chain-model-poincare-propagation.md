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

*Proof sketch.* Each of $\varphi_i$, $b_i$, $H_i$ and $H'_i$ is a sum, over pairs of summands, of signed composites of a block projection, transports, a Kronecker product of factor blocks and a block inclusion (by the definitions of the [product of structures](../tensor/structure-products/based-str-prod.md), the [product of duality maps](../tensor/structure-products/based-dual-prod.md), the [tensor](../tensor/based-tensor-hom.md) and the [dual tensor](../tensor/based-dual-tensor-hom.md) of graded maps). Label a summand $C_p\boxtimes E_q$ by combining the labels of the factors with a map that is $1$-Lipschitz for the max distance. Then block projections, inclusions and transports have propagation $0$ ([propagation of the identity](../../../categories/asymptotic/prop-one.md)), a Kronecker product has at most the larger propagation of its factors, and sums, signs and composites are bounded by [propagation of a sum](../../../categories/asymptotic/prop-add.md), [of a scalar multiple](../../../categories/asymptotic/prop-smul.md) and [of a product](../../../categories/asymptotic/prop-mul.md). On the grid the labels are the [cube centers](../cubical/grid-cube.md) of the [cells](../cubical/grid-cell.md), combined by adding a coordinate (the sup metric of the torus); the [chain-model labels](../model/chain-model-label.md) forget the $\mathbb{CP}^2$ factor. By induction over the circle factors, with $\varphi^s$, $b$, $K$, $K'$ of propagation at most $2/k_i$ ([circle duality](../circle-duality.md) (5)), $\varphi$ and $b$ have propagation at most $2/k_i$ and $H$, $H'$ at most $4/k_i$, through [$A=\varphi^sb$](grid-factor/circle-a.md) and [$A'=b\varphi^s$](grid-factor/circle-a-dual.md).

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

- [Propagation of a sum](../../../categories/asymptotic/prop-add.md)
- [Propagation of a product](../../../categories/asymptotic/prop-mul.md)
- [Propagation of a scalar multiple](../../../categories/asymptotic/prop-smul.md)
- [Propagation of the identity](../../../categories/asymptotic/prop-one.md)
- [Circle duality](../circle-duality.md)
- [Product of structures in explicit bases](../tensor/structure-products/based-str-prod.md)
- [Product of duality maps in explicit bases](../tensor/structure-products/based-dual-prod.md)
- [Tensor of graded maps of based complexes](../tensor/based-tensor-hom.md)
- [Dual tensor of graded maps of based complexes](../tensor/based-dual-tensor-hom.md)
- [Torus labels of chain-model cells](../model/chain-model-label.md)
- [The cube of a basis vector](../cubical/grid-cell.md)
- [Grid cubes](../cubical/grid-cube.md)
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
