---
article_id: af_9396dafecc6f9bc4d2599d25
declaration: lemma
origin: bridged
statement: formalized
lean: HSP.ChainModels.chainModel_poincare_propagation
---

# The chain model is Poincaré: propagation

For every $i$, with cells and duals of the [chain model](../chain-model.md) labelled at their centers, the structure $\varphi_i$ and the map $b_i$ of [chain-model duality](../chain-model-duality.md), the [homotopy](chain-model-h.md) $H_i$ and the [dual homotopy](chain-model-h-dual.md) $H'_i$ have $d_\infty$-[propagation](../../../categories/asymptotic/propagation.md) at most $h_i=4/k_i$.

*Planned route.* Every block of $\varphi_i$, $b_i$, $H_i$ and $H'_i$ is, up to sign, a Kronecker product of blocks of the factors ([blocks of a product of structures](../tensor/structure-products/str-prod-blocks.md), [blocks of a product of duality maps](../tensor/structure-products/dual-prod-blocks.md), [blocks of a tensor of graded maps](../tensor/tensor-hom-blocks.md), [blocks of the dual tensor](../tensor/structure-products/dual-tensor-hom-blocks.md)). A Kronecker product moves each coordinate of a center only by its own factor, so its $d_\infty$-propagation is the maximum of the factor propagations. On the circle, $\varphi^s$, $b$, $K$ and $K'$ have propagation at most $2/k_i$ ([circle duality](../circle-duality.md) (5)), so $A=\varphi^sb$ and $A'=b\varphi^s$ have at most $4/k_i$ ([propagation of a product](../../../categories/asymptotic/prop-mul.md)); the $\mathbb{CP}^2$ factor does not move the torus coordinate. Sums and signs do not increase propagation ([propagation of a sum](../../../categories/asymptotic/prop-add.md)).

## Sources

- New: the explicit chain model of the cubical grid.

## Depends on

- [Chain model](../chain-model.md)
- [Chain-model duality](../chain-model-duality.md)
- [The homotopy of the chain model](chain-model-h.md)
- [The dual homotopy of the chain model](chain-model-h-dual.md)
- [Propagation](../../../categories/asymptotic/propagation.md)
