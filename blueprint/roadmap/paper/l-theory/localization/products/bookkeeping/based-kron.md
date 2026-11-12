---
article_id: af_9dd8f0b851c806abce7a3732
declaration: def
origin: background
statement: formalized
lean: HSP.basedKron
---

# Kronecker product of matrices

For morphisms $f:\mathbb Q^a\to\mathbb Q^{a'}$ and $g:\mathbb Q^b\to\mathbb Q^{b'}$ of the [category of based vector spaces](based-category.md), the morphism $f\otimes g:\mathbb Q^{ab}\to\mathbb Q^{a'b'}$ is the Kronecker product of the matrices $f$ and $g$: its entry in row $(i-1)b'+j$ and column $(k-1)b+l$ is $f_{ik}g_{jl}$, for $1\le i\le a'$, $1\le j\le b'$, $1\le k\le a$, $1\le l\le b$.

## Sources

- New: the Kronecker product, for the chain models of the chain-model chapter.

## Depends on

- [The category of based ℚ-vector spaces](based-category.md)
