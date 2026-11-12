---
article_id: af_646739667d9d57a39830c1d9
declaration: def
origin: background
statement: formalized
lean: HSP.FreeCat.realMap
---

# The real matrix of a morphism

A morphism $u:M\to N$ of the [free category](../../categories/asymptotic/free-category.md) $\mathrm{Free}(\mathbb Q[G])$ is an equivariant rational matrix with rows indexed by $G\times\{1..N.n\}$ and columns by $G\times\{1..M.n\}$. Its real matrix is the same matrix with the entries viewed in $\mathbb R$, acting on column vectors: the linear map $\mathbb R^{G\times\{1..M.n\}}\to\mathbb R^{G\times\{1..N.n\}}$, $v\mapsto uv$.

## Sources

- New: the base change of the matrices to $\mathbb R$ used by real homology.

## Depends on

- [Free category of a finite group](../../categories/asymptotic/free-category.md)
