---
article_id: af_7ef7ad840239f699cb164bad
declaration: def
origin: background
statement: formalized
lean: HSP.ChainModels.cp2Cells
---

# Cells of CP^2

$P$ is the chain complex of [based vector spaces](../../l-theory/localization/products/based-vector-spaces.md) with $P_r=\mathbb Q e_r$ for $r\in\{0,2,4\}$, zero otherwise, and zero differential. Its structure is $\varphi_P:P^{4-*}\to P$, $e_r^*\mapsto e_{4-r}$, an element of the [structure complex](../../l-theory/base/complexes/structure-complex.md) $M(P)_4$ with $\partial\varphi_P=0$ (all differentials vanish), and its [duality map](../../l-theory/base/complexes/cycle-chain-map.md) is an isomorphism with inverse $b_P=\varphi_P^{-1}$, $e_{4-r}\mapsto e_r^*$. Since $r(4-r)$ is even, $T\varphi_P=\varphi_P$. So $(P,\varphi_P)$ is a strict $4$-dimensional [symmetric Poincaré complex](../../l-theory/base/pairs/symmetric-poincare-complex.md), with $P_r=0$ outside $[0,4]$. The induced form on $P_2$ is $\langle1\rangle$, that is, $\varphi_P:(P_2)^*\to P_2$ is the identity $1\times1$ matrix. The fundamental cycle is $e_4$, and $\varepsilon e_0=1$.

## Sources

- [published: cellular chains of $\mathbb{CP}^2$] [U]

## Depends on

- [Based vector spaces](../../l-theory/localization/products/based-vector-spaces.md)
- [Symmetric Poincaré complex](../../l-theory/base/pairs/symmetric-poincare-complex.md)
- [Structure complex](../../l-theory/base/complexes/structure-complex.md), [duality map of a cycle](../../l-theory/base/complexes/cycle-chain-map.md)
