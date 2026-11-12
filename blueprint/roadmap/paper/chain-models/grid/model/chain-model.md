---
article_id: af_1291e7847ad87f559122e709
declaration: def
origin: bridged
statement: formalized
lean: HSP.ChainModels.chainModel
---
# Chain model

Fix a local datum in dimension $n$, so that the [mesh sequence](../mesh-sequence.md) $k_i$ is defined. $D_i=C(k_i)\otimes P$, the [tensor product of based complexes](../based-complex-tensor.md) of the grid complex $C(k_i)$ and the [cellular chain complex $P$ of CP^2](../cp2/cp2-complex.md), with bases enumerated as in the [cubical torus grid](../cubical/cubical-torus-grid.md), with the tensor differential $d\otimes1+(-1)^p1\otimes d$ on $C(k_i)_p\otimes P_q$ and basis cells $c\otimes e_r$.

## Sources
- HS paper, Section 9 (common models).
## Depends on
- [The cellular chain complex of CP^2](../cp2/cp2-complex.md)
- [The cells of CP^2 vanish in negative degrees](../cp2/cp2-dim-neg.md)
- [Cubical torus grid](../cubical/cubical-torus-grid.md), [cells of CP^2](../cp2/cp2-cells.md), [mesh sequence](../mesh-sequence.md), [tensor product of based complexes](../based-complex-tensor.md), [tensor product of based vector spaces](../../../l-theory/localization/products/based-tensor.md)
