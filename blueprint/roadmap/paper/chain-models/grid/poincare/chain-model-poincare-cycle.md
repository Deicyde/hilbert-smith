---
article_id: af_7a95e9e4225f9af401e70455
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.ChainModels.chainModel_poincare_cycle
---

# The chain model is Poincaré: the cycle

For every $i$, the structure $\varphi_i$ of [chain-model duality](../chain-model-duality.md) satisfies $\partial\varphi_i=0$ and $T\varphi_i=\varphi_i$.

*Proof sketch.* Induct over the circle factors. For $\varphi_i=\varphi^{(n)}\otimes\varphi_P$ with $\varphi^{(n+1)}=\varphi^{(n)}\otimes\varphi^s$ and $\varphi^{(0)}$ the identity structure of the unit complex (zero differential, degree $0$), the [Leibniz rule](../tensor/structure-products/str-prod-leibniz.md) gives $\partial(\varphi\otimes\theta)=\partial\varphi\otimes\theta\pm\varphi\otimes\partial\theta=0$ from $\partial\varphi^s=0$ ([circle duality](../circle-duality.md) (2)) and $\partial\varphi_P=0$ ([cells of CP^2](../cp2/cp2-cells.md)); a product with a zero factor vanishes ([left](../tensor/structure-products/str-prod-zero-left.md), [right](../tensor/structure-products/str-prod-zero-right.md)), and the [unit structure is a cycle](../tensor/structure-products/unit-structure-cycle.md). Likewise [products commute with T](../tensor/structure-products/str-prod-involution.md), with $T\varphi^s=\varphi^s$ and $T\varphi_P=\varphi_P$.

## Sources

- New: the explicit chain model of the cubical grid.

## Depends on

- [The structure of the unit complex](../model/unit-structure.md)
- [The structure of the grid complex](../model/grid-structure.md)
- [The cellular chain complex of CP^2](../cp2/cp2-complex.md)
- [The structure of CP^2](../cp2/cp2-structure.md)
- [The circle complex](../cubical/circle-complex.md)
- [The circle complex vanishes in negative degrees](../cubical/circle-dim-neg.md)
- [The unit complex](../cubical/unit-complex.md)
- [Cubical torus grid](../cubical/cubical-torus-grid.md)
- [Chain-model duality](../chain-model-duality.md)
- [The involution T](../../../l-theory/base/complexes/structure-involution.md)

## Proof depends on

- [Leibniz rule for products of structures](../tensor/structure-products/str-prod-leibniz.md)
- [Products of structures commute with T](../tensor/structure-products/str-prod-involution.md)
- [Circle duality](../circle-duality.md)
- [Cells of CP^2](../cp2/cp2-cells.md)
- [The cells of CP^2 vanish in negative degrees](../cp2/cp2-dim-neg.md)
- [A product of structures with a zero left factor](../tensor/structure-products/str-prod-zero-left.md)
- [A product of structures with a zero right factor](../tensor/structure-products/str-prod-zero-right.md)
- [The unit structure is a cycle](../tensor/structure-products/unit-structure-cycle.md)
