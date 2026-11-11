---
article_id: af_b429983bfcac4681e6cb33eb
declaration: lemma
origin: bridged
statement: formalized
lean: HSP.ChainModels.chainModel_poincare_inverse
---

# The chain model is Poincaré: the inverse and the homotopies

For every $i$, with $d$ the differential of $D_i$ and of $D_i^{N-*}$ (on the latter $d_r=(-1)^rd^*$), the map $b_i$ of [chain-model duality](../chain-model-duality.md) is a chain map, and it is the exact inverse of $(\varphi_i^u)_\natural$ for the [unsymmetrized structure](chain-model-structure-u.md) $\varphi_i^u$. The [homotopy](chain-model-h.md) $H_i$ and the [dual homotopy](chain-model-h-dual.md) $H'_i$ satisfy $\varphi_ib_i-1=dH_i+H_id$ and $b_i\varphi_i-1=dH'_i+H'_id$.

## Sources

- New: the explicit chain model of the cubical grid.

## Depends on

- [Chain-model duality](../chain-model-duality.md)
- [The unsymmetrized structure of the chain model](chain-model-structure-u.md)
- [The homotopy of the chain model](chain-model-h.md)
- [The dual homotopy of the chain model](chain-model-h-dual.md)
- [Dual complex](../../../l-theory/base/complexes/dual-complex.md)
