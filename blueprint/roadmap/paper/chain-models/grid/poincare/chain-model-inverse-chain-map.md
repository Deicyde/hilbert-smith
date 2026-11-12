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

*Proof sketch.* The [unsymmetrized structure](chain-model-structure-u.md) $\varphi^u_i$ is a [cycle](chain-model-structure-u-cycle.md), so its [duality map](../../../l-theory/base/complexes/cycle-chain-map.md) is a chain map, and $b_i$ is its exact inverse in every degree ([the chain-model inverse is exact](chain-model-inverse-exact.md)): $bd=bd\varphi^ub=b\varphi^udb=db$.

## Sources

- New: the explicit chain model of the cubical grid.

## Depends on

- [Chain-model duality](../chain-model-duality.md)
- [Chain model](../model/chain-model.md)
- [Dual complex](../../../l-theory/base/complexes/dual-complex.md)
- [Local datum](../../../local-data/chart/local-datum.md)

## Proof depends on

- [The unsymmetrized structure of the chain model is a cycle](chain-model-structure-u-cycle.md)
- [Duality map of a cycle](../../../l-theory/base/complexes/cycle-chain-map.md)
- [The chain-model inverse is exact](chain-model-inverse-exact.md)
- [The unsymmetrized structure of the chain model](chain-model-structure-u.md)
