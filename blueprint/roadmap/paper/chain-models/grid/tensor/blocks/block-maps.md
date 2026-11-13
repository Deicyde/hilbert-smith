---
article_id: af_e2f57d037bd8759c613ec9ba
declaration: def
origin: background
statement: formalized
lean: HSP.ChainModels.blockInc, HSP.ChainModels.blockProj
---

# Block inclusions and projections

Let $d_1,\dots,d_m\in\mathbb N$, and let $\mathbb Q^{\sum_jd_j}$ in the [category of based vector spaces](../../../../l-theory/localization/products/bookkeeping/based-category.md) be the concatenation of the blocks $\mathbb Q^{d_j}$ in increasing order of $j$: the $b$-th basis vector of block $j$ is the basis vector at position $d_1+\dots+d_{j-1}+b$. The *block inclusion* $\iota_j:\mathbb Q^{d_j}\to\mathbb Q^{\sum_jd_j}$ is the matrix whose entry at $(a,b)$ is $1$ if $a$ is the position of the $b$-th basis vector of block $j$, and $0$ otherwise. The *block projection* $\pi_j:\mathbb Q^{\sum_jd_j}\to\mathbb Q^{d_j}$ is its transpose.

## Sources

- New: explicit bases of concatenated sums.

## Depends on

- [The category of based ℚ-vector spaces](../../../../l-theory/localization/products/bookkeeping/based-category.md)
