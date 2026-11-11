---
article_id: af_da78f7f3c550180fc168b9c1
declaration: lemma
origin: background
statement: formalized
proof: formalized
lean: HSP.ChainModels.blockInc_proj
---

# Block projections of the inclusions

Let $\mathbb Q^{\sum_jd_j}$ be the concatenation of the blocks $\mathbb Q^{d_j}$, in increasing order of $j$, as in the [tensor product of based complexes](based-complex-tensor.md), with block inclusions $\iota_j$ and projections $\pi_j$. Then $\pi_{j'}\iota_j=\delta_{jj'}$: $\pi_j\iota_j=1$, and $\pi_{j'}\iota_j=0$ for $j\ne j'$.

*Proof.* The entry of $\pi_{j'}\iota_j$ at $(b',b)$ is $1$ if the basis vector $b$ of block $j$ and $b'$ of block $j'$ are the same basis vector of the concatenation, that is, if $j=j'$ and $b=b'$, and $0$ otherwise.

## Sources

- New: explicit bases of concatenated sums.

## Depends on

- [Tensor product of based complexes](based-complex-tensor.md)
