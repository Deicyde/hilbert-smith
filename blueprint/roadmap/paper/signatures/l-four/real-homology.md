---
article_id: af_32082f34b5cafd779232ab8f
declaration: abbrev
origin: background
statement: formalized
lean: HSP.realH
---

# Real homology

Let $C$ be a chain complex in $\mathrm{Kar}\,\mathrm{Free}(\mathbb Q[G])$ with $C_r=(n_r,e_r)$, over the [free category](../../categories/asymptotic/free-category.md). Its real homology $H_r(C;\mathbb R)$ is the homology in degree $r$ of the real complex $C_r(\mathbb R)=\mathrm{im}(e_r)\subset\mathbb R^{G\times\{1..n_r\}}$ with differential $d$: cycles in $\mathrm{im}(e_r)\cap\ker d$ modulo $d(\mathrm{im}\,e_{r+1})$. It is a functor of $C$: a chain map $f$ induces $f_*$. $G$ acts on $H_r(C;\mathbb R)$ by permuting the basis, $a(g,k)=(a+g,k)$ in the additive notation of the free category, which commutes with the equivariant $e_r$ and $d$.

The real cohomology $H^r(C;\mathbb R)$ is the cohomology in degree $r$ of the real cochains $\mathrm{im}(e_r^T)\subset\mathbb R^{G\times\{1..n_r\}}$ with coboundary $d^T$: cocycles in $\mathrm{im}(e_r^T)\cap\ker d^T$ modulo $d^T(\mathrm{im}\,e_{r-1}^T)$. A chain map $f$ induces $f^*$ on real cohomology by the transposed matrices, and $G$ acts on $H^r(C;\mathbb R)$ by permuting the basis in the same way. Since the [dual complex](../../l-theory/base/complexes/dual-complex.md) $C^{-*}$ has $(C^{-*})_{-r}=(n_r,e_r^T)$ and differential $\pm d^T$, this is $H_{-r}(C^{-*};\mathbb R)$.

## Sources

- [Ranicki 1980 Part I, §1](../../../../sources/paper/ranicki-1980.md) [U]

## Depends on

- [Free category of a finite group](../../categories/asymptotic/free-category.md)
- [Idempotent completion with duality](../../l-theory/base/categories/karoubi-duality.md)
- [Dual complex](../../l-theory/base/complexes/dual-complex.md)
