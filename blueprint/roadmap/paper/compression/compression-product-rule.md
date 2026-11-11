---
article_id: af_b0df007bc8c5ae00fb70fedd
declaration: lemma
origin: bridged
statement: formalized
lean: HSP.Compression.product_rule
proof: formalized
---
# Product rule

Let $M_0,M_1,M_2\in\{D_i,D_i^{N-*}\}$ and $i\ge i_0$. On each $M_j$ let $p_j,\jmath_j$ be the retained projection and inclusion, as in [compressed maps](compressed-maps.md), and let $Q_1=1-\jmath_1p_1$ (that is, $Q_i$ on chains and $Q_i^*$ on cochains). For matrices $\alpha:M_1\to M_2$ and $\beta:M_0\to M_1$,
$$\hat\alpha\,\hat\beta-\widehat{\alpha\beta}=-p_2\,\alpha\,Q_1\,\beta\,\jmath_0 .$$

*Proof sketch.* $\hat\alpha\hat\beta=p_2\alpha(\jmath_1p_1)\beta\jmath_0$; substitute $\jmath_1p_1=1-Q_1$. On cochains, $\mathrm{pr}^*\mathrm{in}^*=(\mathrm{in}\,\mathrm{pr})^*=1-Q^*$.

## Sources
- HS paper, Section 10.

## Depends on

- [Compressed maps](compressed-maps.md)
- [Retained projection](retained-projection.md)
