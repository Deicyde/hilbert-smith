---
article_id: af_c14a1958aaa5b37d4eb696bb
declaration: def
origin: background
statement: formalized
lean: HSP.ChainModels.Torus.dist₂
---

# The quotient Euclidean metric

For $x,y\in\mathbb T^n$ put $d_2(x,y)=\bigl(\sum_jd(x_j,y_j)^2\bigr)^{1/2}$, where $d$ is the circle distance on $\mathbb R/4\mathbb Z$.

**Remark (not formalized).** $d_\infty\le d_2\le\sqrt n\,d_\infty$: each $d(x_j,y_j)^2$ is at most the sum of all of them, and the sum is at most $n\,d_\infty(x,y)^2$.

## Sources

- New: the torus closing of the chart cube $[-2,2]^n$.

## Depends on

- [The torus](../grid/torus.md)
