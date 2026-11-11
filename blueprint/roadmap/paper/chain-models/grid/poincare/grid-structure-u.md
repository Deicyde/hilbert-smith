---
article_id: af_6516fa989d6b59dca42e66aa
declaration: def
origin: bridged
statement: formalized
lean: HSP.ChainModels.gridStructureU
---

# The unsymmetrized grid structure

For $k\ge1$, the unsymmetrized structure $\varphi^u_n\in M(C(k))_n$ of the [grid complex](../cubical-torus-grid.md) is defined by $\varphi^u_0=\mathbb 1$, the identity of $\mathbb Q$ in degree $0$ on the unit complex, and $\varphi^u_{n+1}=\varphi^u_n\otimes\varphi$, the [product of structures](../tensor/structure-products/based-str-prod.md) with the [circle structure](circle-data/circle-phi.md) $\varphi\in M(S_k)_1$. So $\varphi^u_n=(\cdots(\varphi\otimes\varphi)\otimes\cdots)\otimes\varphi$.

## Sources

- New: the explicit chain model of the cubical grid.

## Depends on

- [Cubical torus grid](../cubical-torus-grid.md)
- [Product of structures in explicit bases](../tensor/structure-products/based-str-prod.md)
- [The circle structure](circle-data/circle-phi.md)
- [Chain-model duality](../chain-model-duality.md)
