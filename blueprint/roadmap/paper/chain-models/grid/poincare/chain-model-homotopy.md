---
article_id: af_270bde5c92b9b102b3d4a9a7
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.ChainModels.chainModel_homotopy
---

# The chain-model homotopy

For every $i$, with $d$ the differential of the [chain model](../model/chain-model.md) $D_i$, the structure $\varphi_i$ and the map $b_i$ of [chain-model duality](../chain-model-duality.md) and the [homotopy](chain-model-h.md) $H_i$ satisfy $\varphi_ib_i-1=dH_i+H_id$ on $D_i$.

*Proof sketch.* By [a product of structures after a product of duality maps](../tensor/structure-products/dual-prod-comp-str-prod.md), $\varphi_ib_i=A_n\otimes\varphi_Pb_P$ with $A_n=\varphi_nb$ on the grid, and $\varphi_Pb_P=1$ ([the CP^2 inverse inverts the structure](cp2-inverse.md)). By the [tensor product of homotopies](tensor-homotopy.md), $A_{n+1}-1=dH^{(n+1)}+H^{(n+1)}d$ follows from the same for $A_n$ and $A-1=dK+Kd$ ([circle duality](../circle-duality.md) (3)), with the recursion $H^{(n+1)}=H^{(n)}\otimes A+1\otimes K$ of the [grid homotopy](grid-factor/grid-h.md); it starts from $A_0=1$ ([the grid duality map inverts the unsymmetrized grid structure](grid-factor/grid-inverse.md); the two structures agree on the unit complex) and $H^{(0)}=0$. Once more with $g=\varphi_Pb_P=1$ and $k=0$ (a tensor with a zero factor vanishes, by [additivity](../tensor/tensor-hom-add-right.md)) it gives $\varphi_ib_i-1=dH_i+H_id$ for $H_i=H^{(n)}\otimes1$.

## Sources

- New: the explicit chain model of the cubical grid.

## Depends on

- [Chain-model duality](../chain-model-duality.md)
- [Chain model](../model/chain-model.md)
- [The homotopy of the chain model](chain-model-h.md)
- [Local datum](../../../local-data/chart/local-datum.md)

## Proof depends on

- [The iterated grid duality map](grid-factor/grid-dual-map.md)
- [A product of structures after a product of duality maps](../tensor/structure-products/dual-prod-comp-str-prod.md)
- [The CP^2 inverse inverts the structure](cp2-inverse.md)
- [Tensor product of homotopies](tensor-homotopy.md)
- [Circle duality](../circle-duality.md)
- [The grid homotopy](grid-factor/grid-h.md)
- [The degree-zero map A of the circle](grid-factor/circle-a.md)
- [The grid duality map inverts the unsymmetrized grid structure](grid-factor/grid-inverse.md)
- [The grid complex vanishes in negative degrees](grid-factor/grid-dim-neg.md)
- [Additivity of tensors of graded maps in the second factor](../tensor/tensor-hom-add-right.md)
- [The structure of the grid complex](../model/grid-structure.md)
- [Circle inverse](circle-data/circle-b.md)
- [Symmetric circle structure](circle-data/circle-phi-sym.md)
- [The circle homotopy K](circle-data/circle-k.md)
- [The circle complex vanishes in negative degrees](../cubical/circle-dim-neg.md)
- [The identity as a map of degree zero](../tensor/id-deg0.md)
- [The inverse of the structure of CP^2](../cp2/cp2-inverse.md)
- [The structure of CP^2](../cp2/cp2-structure.md)
- [The cells of CP^2 vanish in negative degrees](../cp2/cp2-dim-neg.md)
- [The cellular chain complex of CP^2](../cp2/cp2-complex.md)
- [Cubical torus grid](../cubical/cubical-torus-grid.md)
- [Mesh sequence](../mesh-sequence.md)
- [Tensor of graded maps of based complexes](../tensor/based-tensor-hom.md)
