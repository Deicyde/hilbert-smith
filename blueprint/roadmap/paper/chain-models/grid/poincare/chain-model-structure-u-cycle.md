---
article_id: af_85cc55b957f84a27552edb95
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.ChainModels.chainModelStructureU_cycle
---

# The unsymmetrized structure of the chain model is a cycle

For every $i$, the [unsymmetrized structure](chain-model-structure-u.md) $\varphi_i^u$ of the chain model is a cycle: $\partial\varphi_i^u=0$.

*Proof sketch.* Induct over the circle factors with the [Leibniz rule](../tensor/structure-products/str-prod-leibniz.md), from the [unit structure](../tensor/structure-products/unit-structure-cycle.md), $\partial\varphi=0$ ([circle duality](../circle-duality.md) (1)) and $\partial\varphi_P=0$ ([cells of CP^2](../cp2/cp2-cells.md)); a product with a zero factor vanishes ([left](../tensor/structure-products/str-prod-zero-left.md), [right](../tensor/structure-products/str-prod-zero-right.md)).

## Sources

- New: the explicit chain model of the cubical grid.

## Depends on

- [The unsymmetrized structure of the chain model](chain-model-structure-u.md)
- [Chain model](../model/chain-model.md)
- [Structure complex](../../../l-theory/base/complexes/structure-complex.md)
- [Local datum](../../../local-data/chart/local-datum.md)

## Proof depends on

- [Leibniz rule for products of structures](../tensor/structure-products/str-prod-leibniz.md)
- [The unit structure is a cycle](../tensor/structure-products/unit-structure-cycle.md)
- [Circle duality](../circle-duality.md)
- [Cells of CP^2](../cp2/cp2-cells.md)
- [The cells of CP^2 vanish in negative degrees](../cp2/cp2-dim-neg.md)
- [A product of structures with a zero left factor](../tensor/structure-products/str-prod-zero-left.md)
- [A product of structures with a zero right factor](../tensor/structure-products/str-prod-zero-right.md)
- [The cellular chain complex of CP^2](../cp2/cp2-complex.md)
- [The structure of CP^2](../cp2/cp2-structure.md)
- [The circle complex](../cubical/circle-complex.md)
- [The circle complex vanishes in negative degrees](../cubical/circle-dim-neg.md)
- [Cubical torus grid](../cubical/cubical-torus-grid.md)
- [Mesh sequence](../mesh-sequence.md)
- [The circle structure](circle-data/circle-phi.md)
- [The unsymmetrized grid structure](grid-factor/grid-structure-u.md)
