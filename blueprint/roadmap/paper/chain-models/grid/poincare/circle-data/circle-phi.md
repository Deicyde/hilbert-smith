---
article_id: af_f1ce64e545e561cf4ce452be
declaration: def
origin: bridged
statement: formalized
lean: HSP.ChainModels.circlePhi
---

# The circle structure

For the [circle complex](../../cubical/circle-complex.md) $S=S_k$, the element $\varphi\in M(S)_1$ of the [structure complex](../../../../l-theory/base/complexes/structure-complex.md) given by $\varphi([w]^*)=e_{w-1}$ and $\varphi(e_w^*)=[w]$ for $w\in\mathbb Z/k$: its component $(S_1)^*\to S_0$ is the identity matrix, its component $(S_0)^*\to S_1$ has entry $1$ in row $e_{w-1}$ and column $[w]^*$ and $0$ elsewhere, and its other components are zero.

## Sources

- New: $\varphi$ is slant with the Serre diagonal; see [circle duality](../../circle-duality.md).

## Depends on

- [The circle complex](../../cubical/circle-complex.md)
- [Structure complex](../../../../l-theory/base/complexes/structure-complex.md)
- [Based vector spaces](../../../../l-theory/localization/products/based-vector-spaces.md)
- [The category of based ℚ-vector spaces](../../../../l-theory/localization/products/bookkeeping/based-category.md)

## Proof depends on

- [Small Q-linear category with strict duality](../../../../l-theory/base/categories/duality-category.md)
