---
article_id: af_7ef7ad840239f699cb164bad
declaration: def
origin: background
statement: formalized
lean: HSP.ChainModels.cp2Cells
---

# Cells of CP^2

$P$ is the [cellular chain complex](cp2-complex.md) of $\mathbb{CP}^2$, with $P_r=\mathbb Q e_r$ for $r\in\{0,2,4\}$, zero otherwise, and zero differential. Its [structure](cp2-structure.md) is $\varphi_P:P^{4-*}\to P$, $e_r^*\mapsto e_{4-r}$, an element of the [structure complex](../../../l-theory/base/complexes/structure-complex.md) $M(P)_4$ with $\partial\varphi_P=0$ (all differentials vanish), and its [duality map](../../../l-theory/base/complexes/cycle-chain-map.md) is an isomorphism with [inverse](cp2-inverse.md) $b_P=\varphi_P^{-1}$, $e_{4-r}\mapsto e_r^*$. Since $r(4-r)$ is even, $T\varphi_P=\varphi_P$. So $(P,\varphi_P)$ is a strict $4$-dimensional [symmetric Poincaré complex](../../../l-theory/base/pairs/symmetric-poincare-complex.md), with $P_r=0$ outside $[0,4]$.

**Remark (not formalized).** The induced form on $P_2$ is $\langle1\rangle$, that is, $\varphi_P:(P_2)^*\to P_2$ is the identity $1\times1$ matrix.

## Sources

- [published: cellular chains of $\mathbb{CP}^2$] [U]

## Depends on

- [Based vector spaces](../../../l-theory/localization/products/based-vector-spaces.md)
- [Symmetric Poincaré complex](../../../l-theory/base/pairs/symmetric-poincare-complex.md)
- [The category of based ℚ-vector spaces](../../../l-theory/localization/products/bookkeeping/based-category.md)

## Proof depends on

- [The cellular chain complex of CP^2](cp2-complex.md)
- [The inverse of the structure of CP^2](cp2-inverse.md)
- [The structure of CP^2](cp2-structure.md)
- [Small Q-linear category with strict duality](../../../l-theory/base/categories/duality-category.md)
- [Duality map of a cycle](../../../l-theory/base/complexes/cycle-chain-map.md)
- [Dual complex](../../../l-theory/base/complexes/dual-complex.md)
- [Structure complex](../../../l-theory/base/complexes/structure-complex.md)
- [The involution T](../../../l-theory/base/complexes/structure-involution.md)
