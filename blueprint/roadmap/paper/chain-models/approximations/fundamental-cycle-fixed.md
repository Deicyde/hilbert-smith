---
article_id: af_2a7c09cddd0248f386c202b8
declaration: lemma
origin: bridged
statement: formalized
lean: HSP.ChainModels.approx_fundamentalCycle
---
# Approximations fix the fundamental cycle

Every $N$-cycle of $D_i$ is a rational multiple of $z_i$, and $a_gz_i=z_i$ for $g\in G_i$.

*Proof sketch.* Each $(n-1)$-cube is a face of exactly two top cubes, with opposite signs in $dz(k)$. So an $n$-cycle has equal coefficients on adjacent top cubes, and the grid is connected. Since $P_4=\mathbb Qe_4$ and $P$ has zero differential, the $N$-cycles are the multiples of $z_i$, and $a_gz_i=\lambda z_i$ for some $\lambda\in\mathbb Q$.

Let $c_\star$ be a top cube with $(2,\dots,2)\in|c_\star|$; it exists for every $k$. Every point of $\overline B(0,3/2)$ has all coordinates in $[-3/2,3/2]$, so it lies at $d_\infty$-distance at least $1/2$ from $(2,\dots,2)$. Since $h_i\le1/128$ by the [mesh sequence](../grid/mesh-sequence.md), $|c_\star|$ misses the ball, so $c_\star\in E(k_i)$ and $a_gc_\star=c_\star$.

Let $e$ be a top cube whose closed cube meets $\overline B(0,3/2)$, and $L=\widehat{r_i(g)}$. By [box hull properties](../grid/box-hull-properties.md) (2), $|\Gamma_L(e)|$ has $d_\infty$-diameter at most $\omega(h_i)+4h_i$ and contains $L|e|$. By [properties](completed-maps-properties.md) (2), $L$ moves points by at most $2D$ in the $\ell^2$ distance $d_2$ of the torus, hence also in $d_\infty$, since each coordinate distance $d(x_j,y_j)$ is at most $d_2(x,y)$. So every point of $|\Gamma_L(e)|$ lies within $\omega(h_i)+5h_i+2D\le1/16+1/32<1/2$ of the ball, and $c_\star\notin\Gamma_L(e)$. Hence the coefficient of $c_\star$ in $a_gz(k_i)$ comes only from $c_\star$ itself and equals $1$, as in $z(k_i)$. So $\lambda=1$.

## Sources
- New: replaces the degree argument of HS paper, Section 9.
## Depends on

- [Fundamental cycle of the chain model](../grid/model/chain-model-fundamental.md)
- [Group approximations](group-approx.md)
- [Chain model](../grid/model/chain-model.md)
- [The category of based ℚ-vector spaces](../../l-theory/localization/products/bookkeeping/based-category.md)
- [Local datum](../../local-data/chart/local-datum.md)

## Proof depends on

- [Chain approximations exist](chain-approx-exists.md)
- [Carried group approximations](group-approx-carried.md)
- [Box hull properties](../grid/box-hull-properties.md)
- [Properties of completed maps](completed-maps-properties.md)
- [Mesh sequence](../grid/mesh-sequence.md)
