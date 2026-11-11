---
article_id: af_a36eab1b7a9b3cb2b37d5c6f
declaration: def
origin: bridged
statement: formalized
lean: HSP.ChainModels.torusTestMap
---
# Torus test map

For $x\in \mathbb T^n$ let $\tilde x\in[-2,2)^n$ be its lift ([the torus](../grid/torus.md)). Given a local datum and a radius $\rho$, define $f_T:\mathbb T^n\to S^n$ by $f_T(x)=f(\tilde x)$, where $f$ is the [test map](../../local-data/chart/test-map.md) of radius $\rho$. For $r<2$ the balls $B(0,r)$ and $\overline B(0,r)$ of $\mathbb R^n$ also denote their images under $q$ in $\mathbb T^n$.

## Sources
- New: the torus closing of the chart cube.
## Depends on
- [Test map](../../local-data/chart/test-map.md)
- [The torus](../grid/torus.md)
