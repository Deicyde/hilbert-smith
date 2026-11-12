---
article_id: af_df6043d834fca93e984139a7
declaration: def
origin: bridged
statement: formalized
lean: HSP.ChainModels.basedDualProd
---

# Product of duality maps in explicit bases

Let $C$ and $E$ be complexes of based vector spaces, $E$ vanishing in negative degrees, and let $f_r:C_r\to C_{m-r}^*$ and $g_r:E_r\to E_{m'-r}^*$ be graded maps, $k=m+m'$. Their product is the map $\Xi^{-1}(f\otimes g):C\otimes E\to(C\otimes E)^{k-*}$ of the [tensor product of based complexes](../../based-complex-tensor.md) whose block from $C_a\boxtimes E_c$ to the dual of $C_{m-a}\boxtimes E_{m'-c}$ is $(-1)^{c(a+m)}f_a\boxtimes g_c$, all other blocks being zero.

## Sources

- New: block calculus for the explicit bases of the chain models.

## Depends on

- [Tensor product of based complexes](../../based-complex-tensor.md)
- [Tensor product of based vector spaces](../../../../l-theory/localization/products/based-tensor.md)
