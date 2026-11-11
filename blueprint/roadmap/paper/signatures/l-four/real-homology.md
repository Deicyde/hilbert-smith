---
article_id: af_32082f34b5cafd779232ab8f
declaration: def
origin: background
---

# Real homology

Let $C$ be a chain complex in $\mathrm{Kar}\,\mathrm{Free}(\mathbb Q[G])$ with $C_r=(n_r,e_r)$, over the [free category](../../categories/asymptotic/free-category.md). Its real homology $H_r(C;\mathbb R)$ is the homology in degree $r$ of the real complex $C_r(\mathbb R)=\mathrm{im}(e_r)\subset\mathbb R^{G\times\{1..n_r\}}$ with differential $d$. It is a functor of $C$: a chain map $f$ induces $f_*$. $G$ acts on $H_r(C;\mathbb R)$ by permuting the basis, $a(g,k)=(ag,k)$, which commutes with the equivariant $e_r$ and $d$.

The real cohomology is $H^r(C;\mathbb R)=H_{-r}(C^{-*};\mathbb R)$, with $C^{-*}$ the [dual complex](../../l-theory/base/complexes/dual-complex.md). Since $(C^{-*})_{-r}=(n_r,e_r^T)$ and its differential is $\pm d^T$, $H^r(C;\mathbb R)$ is the cohomology of $\mathrm{im}(e_r^T)$ with coboundary $d^T$.

## Sources

- [Ranicki 1980 Part I, §1](../../../../sources/paper/ranicki-1980.md) [U]

## Depends on

- [Free category of a finite group](../../categories/asymptotic/free-category.md)
- [Idempotent completion with duality](../../l-theory/base/categories/karoubi-duality.md)
- [Dual complex](../../l-theory/base/complexes/dual-complex.md)
