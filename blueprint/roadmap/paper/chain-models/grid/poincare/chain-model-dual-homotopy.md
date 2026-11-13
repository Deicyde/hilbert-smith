---
article_id: af_5e8da7328d0f1809f776af82
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.ChainModels.chainModel_dual_homotopy
---

# The chain-model dual homotopy

For every $i$, with $d$ the differential of the [dual complex](../../../l-theory/base/complexes/dual-complex.md) $D_i^{N-*}$ ($d_r=(-1)^rd^*$, $N=n+4$), the structure $\varphi_i$ and the map $b_i$ of [chain-model duality](../chain-model-duality.md) and the [dual homotopy](chain-model-h-dual.md) $H'_i$ satisfy $b_i\varphi_i-1=dH'_i+H'_id$ on $D_i^{N-*}$.

*Proof sketch.* First $H'_i=b_iH_i\varphi_i^u$: by [a tensor between a product of structures and a product of duality maps](../tensor/structure-products/str-prod-tensor-dual-prod.md), $b(H^{(n)}\otimes A+1\otimes K)\varphi^u=\Xi^{-1}(bH^{(n)}\varphi^u_n\otimes bA\varphi+b\varphi^u_n\otimes bK\varphi)\Xi$, and on the circle $bA\varphi=b\varphi^s=A'$ and $bK\varphi=\tfrac12bH=K'$ since $\varphi b=1$ ([circle duality](../circle-duality.md) (1)), while $b\varphi^u_n=1$ ([the unsymmetrized grid structure inverts the grid duality map](grid-factor/grid-inverse-right.md)); induct over the circle factors, and finish with $b_P\varphi_P=1$ ([the CP^2 inverse inverts the structure](cp2-inverse.md)). Then, with $b_i\varphi_i^u=1$ ([the chain-model inverse is exact](chain-model-inverse-exact.md)), $b_i$ a chain map ([the chain-model inverse is a chain map](chain-model-inverse-chain-map.md)) and $(\varphi_i^u)_\natural$ a chain map ([the unsymmetrized structure is a cycle](chain-model-structure-u-cycle.md)), the [chain-model homotopy](chain-model-homotopy.md) gives $b\varphi-1=b(\varphi b-1)\varphi^u=b(dH+Hd)\varphi^u=dH'+H'd$.

## Sources

- New: the explicit chain model of the cubical grid.

## Depends on

- [Chain-model duality](../chain-model-duality.md)
- [Dual complex](../../../l-theory/base/complexes/dual-complex.md)
- [The dual homotopy of the chain model](chain-model-h-dual.md)
- [Chain model](../model/chain-model.md)
- [Local datum](../../../local-data/chart/local-datum.md)
- [Small Q-linear category with strict duality](../../../l-theory/base/categories/duality-category.md)
- [Based vector spaces](../../../l-theory/localization/products/based-vector-spaces.md)
- [The category of based ℚ-vector spaces](../../../l-theory/localization/products/bookkeeping/based-category.md)

## Proof depends on

- [The iterated grid duality map](grid-factor/grid-dual-map.md)
- [A tensor between a product of structures and a product of duality maps](../tensor/structure-products/str-prod-tensor-dual-prod.md)
- [Circle duality](../circle-duality.md)
- [The unsymmetrized grid structure inverts the grid duality map](grid-factor/grid-inverse-right.md)
- [The grid homotopy](grid-factor/grid-h.md)
- [The dual grid homotopy](grid-factor/grid-h-dual.md)
- [The degree-zero map A of the circle](grid-factor/circle-a.md)
- [The degree-zero map A' of the dual circle](grid-factor/circle-a-dual.md)
- [The grid complex vanishes in negative degrees](grid-factor/grid-dim-neg.md)
- [The CP^2 inverse inverts the structure](cp2-inverse.md)
- [The chain-model inverse is exact](chain-model-inverse-exact.md)
- [The chain-model inverse is a chain map](chain-model-inverse-chain-map.md)
- [The unsymmetrized structure of the chain model is a cycle](chain-model-structure-u-cycle.md)
- [The chain-model homotopy](chain-model-homotopy.md)
- [The homotopy of the chain model](chain-model-h.md)
- [Duality map of a cycle](../../../l-theory/base/complexes/cycle-chain-map.md)
- [The circle homotopy](circle-data/circle-k.md)
- [The dual circle homotopy](circle-data/circle-k-dual.md)
- [The identity as a map of degree zero](../tensor/id-deg0.md)
- [The identity of a dual complex as a map of degree zero](grid-factor/id-dual-deg0.md)
- [Tensor product of based complexes](../based-complex-tensor.md)
- [The cellular chain complex of CP^2](../cp2/cp2-complex.md)
- [The cells of CP^2 vanish in negative degrees](../cp2/cp2-dim-neg.md)
- [The inverse of the structure of CP^2](../cp2/cp2-inverse.md)
- [The structure of CP^2](../cp2/cp2-structure.md)
- [The circle complex](../cubical/circle-complex.md)
- [The circle complex vanishes in negative degrees](../cubical/circle-dim-neg.md)
- [Cubical torus grid](../cubical/cubical-torus-grid.md)
- [Mesh sequence](../mesh-sequence.md)
- [The unsymmetrized structure of the chain model](chain-model-structure-u.md)
- [The circle inverse](circle-data/circle-b.md)
- [The circle structure](circle-data/circle-phi.md)
- [The unsymmetrized grid structure](grid-factor/grid-structure-u.md)
- [Tensor of graded maps of based complexes](../tensor/based-tensor-hom.md)
- [Propagation](../../../categories/asymptotic/propagation.md)
- [Augmentation of the circle complex](../cubical/circle-aug.md)
- [Fundamental chain of the circle complex](../cubical/circle-fundamental.md)
- [Labels of the circle cells](../cubical/circle-label.md)
- [The circle homotopy element](circle-data/circle-h.md)
- [The symmetric circle structure](circle-data/circle-phi-sym.md)
- [Dual tensor of graded maps of based complexes](../tensor/based-dual-tensor-hom.md)
- [Product of duality maps in explicit bases](../tensor/structure-products/based-dual-prod.md)
- [Product of structures in explicit bases](../tensor/structure-products/based-str-prod.md)
- [Structure complex](../../../l-theory/base/complexes/structure-complex.md)
- [The involution T](../../../l-theory/base/complexes/structure-involution.md)
