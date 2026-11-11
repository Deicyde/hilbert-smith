---
article_id: af_0c50b954047cef33db175549
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.ChainModels.chainModel_inverse_chainMap
---

# The chain-model inverse is a chain map

For every $i$, with $d$ the differential of $D_i$ and of $D_i^{N-*}$ (on the latter $d_r=(-1)^rd^*$), $N=n+4$, the map $b_i$ of [chain-model duality](../chain-model-duality.md) is a chain map $D_i\to D_i^{N-*}$ of the [chain model](../model/chain-model.md) to its [dual complex](../../../l-theory/base/complexes/dual-complex.md).

*Proof sketch.* The [unsymmetrized structure](chain-model-structure-u.md) $\varphi_i^u$ is a cycle: by the [Leibniz rule](../tensor/structure-products/str-prod-leibniz.md), induction over the circle factors from the [unit structure](../tensor/structure-products/unit-structure-cycle.md), $\partial\varphi=0$ ([circle duality](../circle-duality.md) (1)) and $\partial\varphi_P=0$ ([cells of CP^2](../cp2/cp2-cells.md)), a product with a zero factor vanishing ([left](../tensor/structure-products/str-prod-zero-left.md), [right](../tensor/structure-products/str-prod-zero-right.md)). So its [duality map](../../../l-theory/base/complexes/cycle-chain-map.md) $(\varphi_i^u)_\natural$ is a chain map, and $b_i$ is its exact inverse in every degree ([the chain-model inverse is exact](chain-model-inverse-exact.md)): $bd=bd\varphi^ub=b\varphi^udb=db$.

## Sources

- New: the explicit chain model of the cubical grid.

## Depends on

- [Chain-model duality](../chain-model-duality.md)
- [Chain model](../model/chain-model.md)
- [Dual complex](../../../l-theory/base/complexes/dual-complex.md)

## Proof depends on

- [The unsymmetrized structure of the chain model](chain-model-structure-u.md)
- [Leibniz rule for products of structures](../tensor/structure-products/str-prod-leibniz.md)
- [The unit structure is a cycle](../tensor/structure-products/unit-structure-cycle.md)
- [Circle duality](../circle-duality.md)
- [Cells of CP^2](../cp2/cp2-cells.md)
- [A product of structures with a zero left factor](../tensor/structure-products/str-prod-zero-left.md)
- [A product of structures with a zero right factor](../tensor/structure-products/str-prod-zero-right.md)
- [Duality map of a cycle](../../../l-theory/base/complexes/cycle-chain-map.md)
- [The chain-model inverse is exact](chain-model-inverse-exact.md)
- [The cells of CP^2 vanish in negative degrees](../cp2/cp2-dim-neg.md)
