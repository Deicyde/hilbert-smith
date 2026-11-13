---
article_id: af_ac7990fd3df657bcc779c686
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.ChainModels.chainModel_inverse_exact
---

# The chain-model inverse is exact

For every $i$ and $N=n+4$, the map $b_i$ of [chain-model duality](../chain-model-duality.md) is the exact inverse of $(\varphi_i^u)_\natural$ for the [unsymmetrized structure](chain-model-structure-u.md) $\varphi_i^u$: in every degree $r$, $b_r(\varphi_i^u)_{r,N-r}=1$ on $(D_i)_{N-r}^*$ and $(\varphi_i^u)_{r,N-r}b_r=1$ on $(D_i)_r$.

*Proof sketch.* By [a product of structures after a product of duality maps](../tensor/structure-products/dual-prod-comp-str-prod.md), $(\varphi_i^u)_{r,N-r}b_r$ is the tensor of $\varphi^u_nb$ on the grid and $\varphi_Pb_P$; both are identities ([the grid duality map inverts the unsymmetrized grid structure](grid-factor/grid-inverse.md), [the CP^2 inverse inverts the structure](cp2-inverse.md)), and the [tensor of identities](../tensor/tensor-hom-id.md) is the identity. By [a product of duality maps after a product of structures](../tensor/structure-products/str-prod-comp-dual-prod.md), $b_r(\varphi_i^u)_{r,N-r}$ is the dual tensor of $b\varphi^u_n$ and $b_P\varphi_P$. On the grid $b\varphi^u_n=1$ ([the unsymmetrized grid structure inverts the grid duality map](grid-factor/grid-inverse-right.md)), and $b_P\varphi_P=1$ ([the CP^2 inverse inverts the structure](cp2-inverse.md)); the [dual tensor of identities](../tensor/structure-products/dual-tensor-hom-id.md) is the identity. The grid complex vanishes in negative degrees ([the grid complex vanishes in negative degrees](grid-factor/grid-dim-neg.md)).

## Sources

- New: the explicit chain model of the cubical grid.

## Depends on

- [Chain-model duality](../chain-model-duality.md)
- [The unsymmetrized structure of the chain model](chain-model-structure-u.md)
- [Local datum](../../../local-data/chart/local-datum.md)
- [Chain model](../model/chain-model.md)
- [Small Q-linear category with strict duality](../../../l-theory/base/categories/duality-category.md)
- [Dual complex](../../../l-theory/base/complexes/dual-complex.md)
- [Based vector spaces](../../../l-theory/localization/products/based-vector-spaces.md)
- [The category of based ℚ-vector spaces](../../../l-theory/localization/products/bookkeeping/based-category.md)

## Proof depends on

- [The iterated grid duality map](grid-factor/grid-dual-map.md)
- [The unsymmetrized grid structure inverts the grid duality map](grid-factor/grid-inverse-right.md)
- [A product of structures after a product of duality maps](../tensor/structure-products/dual-prod-comp-str-prod.md)
- [A product of duality maps after a product of structures](../tensor/structure-products/str-prod-comp-dual-prod.md)
- [The grid duality map inverts the unsymmetrized grid structure](grid-factor/grid-inverse.md)
- [The CP^2 inverse inverts the structure](cp2-inverse.md)
- [Tensor of identities](../tensor/tensor-hom-id.md)
- [Dual tensor of identities](../tensor/structure-products/dual-tensor-hom-id.md)
- [The grid complex vanishes in negative degrees](grid-factor/grid-dim-neg.md)
- [The identity of a dual complex as a map of degree zero](grid-factor/id-dual-deg0.md)
- [The identity as a map of degree zero](../tensor/id-deg0.md)
- [The cellular chain complex of CP^2](../cp2/cp2-complex.md)
- [The cells of CP^2 vanish in negative degrees](../cp2/cp2-dim-neg.md)
- [The inverse of the structure of CP^2](../cp2/cp2-inverse.md)
- [The structure of CP^2](../cp2/cp2-structure.md)
- [Cubical torus grid](../cubical/cubical-torus-grid.md)
- [Mesh sequence](../mesh-sequence.md)
- [The unsymmetrized grid structure](grid-factor/grid-structure-u.md)
- [Tensor product of based complexes](../based-complex-tensor.md)
- [Dual tensor of graded maps of based complexes](../tensor/based-dual-tensor-hom.md)
- [Tensor of graded maps of based complexes](../tensor/based-tensor-hom.md)
- [Product of duality maps in explicit bases](../tensor/structure-products/based-dual-prod.md)
- [Product of structures in explicit bases](../tensor/structure-products/based-str-prod.md)
