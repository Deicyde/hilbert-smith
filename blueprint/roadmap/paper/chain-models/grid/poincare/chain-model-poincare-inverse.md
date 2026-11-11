---
article_id: af_b429983bfcac4681e6cb33eb
declaration: lemma
origin: bridged
statement: formalized
lean: HSP.ChainModels.chainModel_poincare_inverse
---

# The chain model is Poincaré: the inverse and the homotopies

For every $i$, with $d$ the differential of $D_i$ and of $D_i^{N-*}$ (on the latter $d_r=(-1)^rd^*$), the map $b_i$ of [chain-model duality](../chain-model-duality.md) is a chain map, and it is the exact inverse of $(\varphi_i^u)_\natural$ for the [unsymmetrized structure](chain-model-structure-u.md) $\varphi_i^u$. The [homotopy](chain-model-h.md) $H_i$ and the [dual homotopy](chain-model-h-dual.md) $H'_i$ satisfy $\varphi_ib_i-1=dH_i+H_id$ and $b_i\varphi_i-1=dH'_i+H'_id$.

*Planned route.* A [product of duality maps composed with a product of structures](../tensor/structure-products/dual-prod-comp-str-prod.md) is the [tensor](../tensor/based-tensor-hom.md) of the factorwise composites, and a [product of structures composed with a product of duality maps](../tensor/structure-products/str-prod-comp-dual-prod.md) is the [dual tensor](../tensor/based-dual-tensor-hom.md) of the factorwise composites. With $\varphi b=1$ and $b\varphi=1$ on the circle ([circle duality](../circle-duality.md) (1)) and $\varphi_Pb_P=1$, $b_P\varphi_P=1$ ([cells of CP^2](../cp2-cells.md)), the [tensor of identities](../tensor/tensor-hom-id.md) gives $(\varphi_i^u)_\natural b_i=1$ and $b_i(\varphi_i^u)_\natural=1$. For the homotopies, $\varphi_ib_i=A^{\otimes n}\otimes1$; write the [differential of a tensor product](../tensor/tensor-differential.md) as $d\otimes1+1\otimes d$, expand with the [composite of tensors](../tensor/based-tensor-hom-comp.md) and [additivity](../tensor/tensor-hom-add-left.md), and use $A-1=dK+Kd$ (circle duality (3)), which also gives $Ad=dA$. Then $d(H\otimes A+1\otimes K)+(H\otimes A+1\otimes K)d=(A^{\otimes n}-1)\otimes A+1\otimes(A-1)$ by induction on $n$. The dual statements and the chain-map property of $b_i$ go the same way through the [blocks of the dual tensor](../tensor/structure-products/dual-tensor-hom-blocks.md) and the [blocks of a product of duality maps](../tensor/structure-products/dual-prod-blocks.md).

## Sources

- New: the explicit chain model of the cubical grid.

## Depends on

- [Chain-model duality](../chain-model-duality.md)
- [The unsymmetrized structure of the chain model](chain-model-structure-u.md)
- [The homotopy of the chain model](chain-model-h.md)
- [The dual homotopy of the chain model](chain-model-h-dual.md)
- [Dual complex](../../../l-theory/base/complexes/dual-complex.md)
