---
article_id: af_32082f34b5cafd779232ab8f
declaration: abbrev
origin: background
statement: formalized
lean: HSP.realH
---

# Real homology

Let $C$ be a chain complex in $\mathrm{Kar}\,\mathrm{Free}(\mathbb Q[G])$ with $C_r=(n_r,e_r)$, over the [free category](../../categories/asymptotic/free-category.md). Its real homology $H_r(C;\mathbb R)$ is the homology in degree $r$ of the real complex $C_r(\mathbb R)=\mathrm{im}(e_r)\subset\mathbb R^{G\times\{1..n_r\}}$ with differential $d$, using the [real matrices](../real/real-matrix.md): the real cycles $\mathrm{im}(e_r)\cap\ker d_r$ modulo the real boundaries $d_{r+1}(\mathrm{im}\,e_{r+1})$.

**Remark (not formalized).** $G$ acts on $H_r(C;\mathbb R)$ by permuting the basis, $a(g,k)=(a+g,k)$ in the additive notation of the free category, which commutes with the equivariant $e_r$ and $d$.

## Sources

- [Ranicki 1980 Part I, §1](../../../../sources/paper/ranicki-1980.md) [U]

## Depends on

- [Free category of a finite group](../../categories/asymptotic/free-category.md)

## Proof depends on

- [The real matrix of a morphism](../real/real-matrix.md)
