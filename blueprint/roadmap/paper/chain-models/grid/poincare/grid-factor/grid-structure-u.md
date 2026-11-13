---
article_id: af_6516fa989d6b59dca42e66aa
declaration: def
origin: bridged
statement: formalized
lean: HSP.ChainModels.gridStructureU
---

# The unsymmetrized grid structure

For every $k$, the unsymmetrized structure $\varphi^u_n\in M(C(k))_n$ of the [grid complex](../../cubical/cubical-torus-grid.md) is defined by $\varphi^u_0=\mathbb 1$, the identity of $\mathbb Q$ in degree $0$ on the unit complex, and $\varphi^u_{n+1}=\varphi^u_n\otimes\varphi$, the [product of structures](../../tensor/structure-products/based-str-prod.md) with the [circle structure](../circle-data/circle-phi.md) $\varphi\in M(S_k)_1$. So $\varphi^u_n=(\cdots(\mathbb 1\otimes\varphi)\otimes\cdots)\otimes\varphi$.

## Sources

- New: the explicit chain model of the cubical grid.

## Depends on

- [Cubical torus grid](../../cubical/cubical-torus-grid.md)
- [Structure complex](../../../../l-theory/base/complexes/structure-complex.md)
- [Based vector spaces](../../../../l-theory/localization/products/based-vector-spaces.md)
- [The category of based ℚ-vector spaces](../../../../l-theory/localization/products/bookkeeping/based-category.md)

## Proof depends on

- [The circle complex](../../cubical/circle-complex.md)
- [The circle complex vanishes in negative degrees](../../cubical/circle-dim-neg.md)
- [The structure of the unit complex](../../model/unit-structure.md)
- [The circle structure](../circle-data/circle-phi.md)
- [Product of structures in explicit bases](../../tensor/structure-products/based-str-prod.md)
