---
article_id: af_e0960f3499258dc93c100414
declaration: def
origin: background
statement: formalized
lean: HSP.ChainModels.realization
---

# Realization of based complexes

The *realization* sends a [based vector space](../../l-theory/localization/products/based-vector-spaces.md) $\mathbb Q^d$ to the $\mathbb Q$-module of functions $\{1,\dots,d\}\to\mathbb Q$ (columns), and a $d'\times d$ matrix $A$ to the linear map $z\mapsto Az$. It preserves identities, composition and sums, so it is an additive functor to $\mathbb Q$-modules. Applied degreewise, it sends a chain complex $C$ of based vector spaces to a rational chain complex with the same differentials acting on columns. The basis of $C_r$ indexes the standard basis of the realization of $C_r$: the basis vector $e_a$ is the column with $1$ in place $a$ and $0$ elsewhere, the coordinates of a column in this basis are its entries, and the coefficient of $e_b$ in $d(e_a)$ is the matrix entry $d_{ba}$.

This lets a complex of based vector spaces, such as the cubical torus grid, be the source or target of a carrier.

## Sources

- New: realizes the explicit based complexes of the chain models as rational chain complexes.

## Depends on

- [Based vector spaces](../../l-theory/localization/products/based-vector-spaces.md)
