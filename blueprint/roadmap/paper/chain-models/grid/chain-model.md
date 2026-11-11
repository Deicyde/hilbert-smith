---
article_id: af_1291e7847ad87f559122e709
declaration: def
origin: bridged
statement: formalized
lean: HSP.ChainModels.chainModel
---
# Chain model

Fix a local datum in dimension $n$, so that the [mesh sequence](mesh-sequence.md) $k_i$ is defined. $D_i=C(k_i)\otimes P$, the [tensor product of based complexes](based-complex-tensor.md) of the grid complex $C(k_i)$ and the [cells of CP^2](cp2/cp2-cells.md), with bases enumerated as in the [cubical torus grid](cubical/cubical-torus-grid.md), with the tensor differential $d\otimes1+(-1)^p1\otimes d$ on $C(k_i)_p\otimes P_q$ and basis cells $c\otimes e_r$. A cell $c\otimes e_r$ and its dual both carry the torus label $x_c$, the center of the cube $c$. The fundamental cycle is the abbreviation $z_i=z(k_i)\otimes e_4\in(D_i)_{n+4}$, in the summand $C(k_i)_n\otimes P_4$.

## Sources
- HS paper, Section 9 (common models).
## Depends on
- [The cellular chain complex of CP^2](cp2/cp2-complex.md)
- [Fundamental cycle of CP^2](cp2/cp2-fundamental.md)
- [Grid cubes](cubical/grid-cube.md)
- [The cube of a basis vector](cubical/grid-cell.md)
- [Fundamental chain of the grid complex](cubical/grid-fundamental.md)
- [The cells of CP^2 vanish in negative degrees](cp2/cp2-dim-neg.md)
- [Cubical torus grid](cubical/cubical-torus-grid.md), [cells of CP^2](cp2/cp2-cells.md), [mesh sequence](mesh-sequence.md), [tensor product of based complexes](based-complex-tensor.md), [tensor product of based vector spaces](../../l-theory/localization/products/based-tensor.md)
