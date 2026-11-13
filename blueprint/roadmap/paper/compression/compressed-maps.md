---
article_id: af_cd214288ab36ac3e7b071271
declaration: def
origin: bridged
statement: formalized
lean: HSP.Compression.compress, HSP.Compression.dHat, HSP.Compression.dHatDual, HSP.Compression.phiHat, HSP.Compression.bHat, HSP.Compression.HHat, HSP.Compression.H'Hat, HSP.Compression.AHat, HSP.Compression.BHat, HSP.Compression.VHat
---
# Compressed maps

Let $M_1,M_2\in\{D_i,D_i^{N-*}\}$, and let $p_2$ be the retained projection of $M_2$ and $\jmath_1$ the retained inclusion of $M_1$: $\mathrm{pr}_i$ and $\mathrm{in}_i$ on chains, $\mathrm{in}_i^*$ and $\mathrm{pr}_i^*$ on cochains ([retained projection](retained-projection.md), [retained inclusion](retained-inclusion.md)). The *compression* of a matrix $w:M_1\to M_2$ is $\hat w=p_2\,w\,\jmath_1$ for $i\ge i_0$, and $\hat w=0$ for $i<i_0$.

The compressed maps are the compressions, for $g,h\in G_i$, of the matrices of the [chain models](../chain-models/grid/model/chain-model.md) and the [approximations](../chain-models/approximations/group-approx.md):
- $\hat d$, of the differential $d$ of $D_i$, and $\hat d^\vee$, of the differential $d$ of the [dual complex](../l-theory/base/complexes/dual-complex.md) $D_i^{N-*}$ (with $d_r=(-1)^rd^*$);
- $\hat\varphi$, $\hat b$, $\hat H$, $\hat H'$, of $\varphi_i$, $b_i$ ([chain-model duality](../chain-models/grid/chain-model-duality.md)), $H_i$ ([homotopy](../chain-models/grid/poincare/chain-model-h.md)), $H'_i$ ([dual homotopy](../chain-models/grid/poincare/chain-model-h-dual.md));
- $\hat A_g$, $\hat B_{g,h}$, $\hat V_g$, of $a_g$, $B_{g,h}$ ([chosen product homotopies](../chain-models/approximations/chosen-product-homotopies.md)), $V_g$ ([adjoint homotopy](../chain-models/approximations/adjoint-homotopy.md)).


**Remark (not formalized).** $\hat d^\vee$ in degree $r$ is $(-1)^r$ times the transpose of $\hat d$ in degree $N-r+1$. Indeed $\mathrm{in}_i=\mathrm{pr}_i^T$, so on cochains the retained projection is $\mathrm{in}_i^*=\mathrm{pr}_i$ and the retained inclusion is $\mathrm{pr}_i^*=\mathrm{in}_i$. The differential of $D_i^{N-*}$ in degree $r$ is $(-1)^r$ times the transpose of $d_{N-r+1}$, the dual of a morphism of based vector spaces being its transpose. Hence $\hat d^\vee_r=(-1)^r\,\mathrm{pr}_i\,d_{N-r+1}^T\,\mathrm{in}_i=(-1)^r(\mathrm{pr}_i\,d_{N-r+1}\,\mathrm{in}_i)^T$. The residual identities do not use this, because they compress the differential of $D_i^{N-*}$ directly. The proof that the compressed complex is Poincaré, which reads them on $C^{N-*}$, argues the identity where it uses it.

## Sources
- HS paper, Section 10.

## Depends on

- [Fixed local data](../local-data/control/fixed-local-data.md)
- [Chain model](../chain-models/grid/model/chain-model.md)
- [The category of based ℚ-vector spaces](../l-theory/localization/products/bookkeeping/based-category.md)
- [Compressed complex](compressed-complex.md)
- [Asymptotic category](../categories/asymptotic/asymptotic-category.md)
- [The trivial group sequence](../categories/asymptotic/trivial-group-sequence.md)
- [The round sphere](../corner/round-sphere.md)
- [The cyclic action on the control space](../local-data/control/control-action.md)
- [The metric on the control space](../local-data/control/control-metric-space.md)
- [The control space](../local-data/control/control-space.md)

## Proof depends on

- [Retained projection](retained-projection.md)
- [Retained inclusion](retained-inclusion.md)
- [Dual complex](../l-theory/base/complexes/dual-complex.md)
- [Chain-model duality](../chain-models/grid/chain-model-duality.md)
- [The homotopy of the chain model](../chain-models/grid/poincare/chain-model-h.md)
- [The dual homotopy of the chain model](../chain-models/grid/poincare/chain-model-h-dual.md)
- [Group approximations](../chain-models/approximations/group-approx.md)
- [Chosen product homotopies](../chain-models/approximations/chosen-product-homotopies.md)
- [The adjoint homotopy](../chain-models/approximations/adjoint-homotopy.md)
- [Based vector spaces](../l-theory/localization/products/based-vector-spaces.md)
