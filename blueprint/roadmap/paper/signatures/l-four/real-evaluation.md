---
article_id: af_5e222be924951f6ccfd35574
declaration: def
origin: background
statement: formalized
lean: HSP.realEval
---

# The evaluation pairing

For a chain complex $C$ in $\mathrm{Kar}\,\mathrm{Free}(\mathbb Q[G])$ with $C_r=(n_r,e_r)$, the evaluation pairing $\langle-,-\rangle:H^r(C;\mathbb R)\times H_r(C;\mathbb R)\to\mathbb R$ on [real cohomology](../real/real-cohomology.md) and [real homology](real-homology.md) is $\langle[x],[y]\rangle=\sum_bx_by_b$ for a cocycle $x\in\mathrm{im}(e_r^T)$ and a cycle $y\in\mathrm{im}(e_r)$, the sum running over $b\in G\times\{1..n_r\}$. It is bilinear.

*Proof sketch.* (Well-definedness.) $\langle d^Tw,y\rangle=\langle w,dy\rangle=0$ for a cycle $y$, and $\langle x,dz\rangle=\langle d^Tx,z\rangle=0$ for a cocycle $x$.

## Sources

- [published: universal coefficients over a field] [U]

## Depends on

- [Real homology](real-homology.md)
- [Real cohomology](../real/real-cohomology.md)
- [The real matrix of a morphism](../real/real-matrix.md)
- [Free category of a finite group](../../categories/asymptotic/free-category.md)
- [Small Q-linear category with strict duality](../../l-theory/base/categories/duality-category.md)
- [Idempotent completion with duality](../../l-theory/base/categories/karoubi-duality.md)
