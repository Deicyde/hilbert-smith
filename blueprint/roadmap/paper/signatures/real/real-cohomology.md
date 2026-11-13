---
article_id: af_1349465e9f51a95358273858
declaration: abbrev
origin: background
statement: formalized
lean: HSP.realHco
---

# Real cohomology

Let $C$ be a chain complex in $\mathrm{Kar}\,\mathrm{Free}(\mathbb Q[G])$ with $C_r=(n_r,e_r)$. Its real cohomology $H^r(C;\mathbb R)$ is the cohomology in degree $r$ of the real cochains $\mathrm{im}(e_r^T)\subset\mathbb R^{G\times\{1..n_r\}}$ with coboundary $d^T$, using the [real matrices](real-matrix.md) of the transposes: the real cocycles $\mathrm{im}(e_r^T)\cap\ker d_{r+1}^T$ modulo the real coboundaries $d_r^T(\mathrm{im}\,e_{r-1}^T)$. In $\mathrm{Kar}\,\mathrm{Free}(\mathbb Q[G])$ the dual of $(n,e)$ is $(n,e^T)$ and the dual of a morphism is its transpose, so $\mathrm{im}(e_r^T)$ is the real space of $C_r^*$ and $d^T$ is the real matrix of $d^*$.

**Remark (not formalized).** Since the dual complex $C^{-*}$ has $(C^{-*})_{-r}=(n_r,e_r^T)$ and differential $\pm d^T$, $H^r(C;\mathbb R)$ is the real homology $H_{-r}(C^{-*};\mathbb R)$.

## Sources

- [Ranicki 1980 Part I, §1](../../../../sources/paper/ranicki-1980.md) [U]

## Depends on

- [Free category of a finite group](../../categories/asymptotic/free-category.md)

## Proof depends on

- [Small Q-linear category with strict duality](../../l-theory/base/categories/duality-category.md)
- [Idempotent completion with duality](../../l-theory/base/categories/karoubi-duality.md)
- [The real matrix of a morphism](real-matrix.md)
