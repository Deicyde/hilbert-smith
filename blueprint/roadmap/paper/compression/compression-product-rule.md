---
article_id: af_b0df007bc8c5ae00fb70fedd
declaration: lemma
origin: bridged
statement: formalized
lean: HSP.Compression.product_rule
proof: formalized
---
# Product rule

Let $M_0,M_1,M_2\in\{D_i,D_i^{N-*}\}$ and $i\in\mathbb N$. On each $M_j$ let $p_j,\jmath_j$ be the retained projection and inclusion, as in [compressed maps](compressed-maps.md), and let $Q_1=1-\jmath_1p_1$ (that is, [$Q_i$](discard-projection.md) on chains and $Q_i^*$ on cochains). For matrices $\alpha:M_1\to M_2$ and $\beta:M_0\to M_1$,
$$\hat\alpha\,\hat\beta-\widehat{\alpha\beta}=-p_2\,\alpha\,Q_1\,\beta\,\jmath_0 .$$

The restriction $i\ge i_0$ is not needed: for $i<i_0$ every compressed rank is $0$ and both sides vanish.

*Proof sketch.* $\hat\alpha\hat\beta=p_2\alpha(\jmath_1p_1)\beta\jmath_0$; substitute $\jmath_1p_1=1-Q_1$. On cochains, $\mathrm{pr}^*\mathrm{in}^*=(\mathrm{in}\,\mathrm{pr})^*=1-Q^*$.

## Sources
- HS paper, Section 10.

## Depends on

- [Fixed local data](../local-data/control/fixed-local-data.md)
- [Chain model](../chain-models/grid/model/chain-model.md)
- [The category of based ℚ-vector spaces](../l-theory/localization/products/bookkeeping/based-category.md)
- [Compressed maps](compressed-maps.md)
- [Retained projection](retained-projection.md)
- [Retained inclusion](retained-inclusion.md)
- [Projection onto the discarded cells](discard-projection.md)
- [Asymptotic category](../categories/asymptotic/asymptotic-category.md)
- [The trivial group sequence](../categories/asymptotic/trivial-group-sequence.md)
- [Compressed complex](compressed-complex.md)
- [The round sphere](../corner/round-sphere.md)
- [The cyclic action on the control space](../local-data/control/control-action.md)
- [The metric on the control space](../local-data/control/control-metric-space.md)
- [The control space](../local-data/control/control-space.md)
