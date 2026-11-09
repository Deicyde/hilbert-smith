---
declaration: lemma
origin: bridged
---
# Approximations fix the fundamental cycle

Every $N$-cycle of $D_i$ is a multiple of $z_i$, and $a_gz_i=z_i$ for $g\in G_i$.

*Proof sketch.* Each $(n-1)$-cube is a face of exactly two top cubes, with opposite signs in $dz(k)$. So an $n$-cycle has equal coefficients on adjacent top cubes, and the grid is connected. Hence $a_gz_i=\lambda z_i$. Let $c_\star$ be any top cube with $(2,\dots,2)\in|c_\star|$; it exists for every $k$. Each point of $\overline B(0,3/2)$ has all coordinates in $[-3/2,3/2]$, so it lies at $d_\infty$-distance at least $1/2$ from $(2,\dots,2)$. Thus $c_\star\in E(k_i)$, and $a_g$ fixes the top cubes of $E(k_i)$. A top cube $e\notin E(k_i)$ meets the ball, so $|\Gamma(e)|$ lies within $2D+3h_i<1/2$ of it, and $c_\star\notin\Gamma(e)$. So the coefficient of $c_\star$ in $a_gz_i$ is $\pm1$, as in $z_i$, and $\lambda=1$.

## Sources
- New: replaces the degree argument of HS paper, Section 9.
## Depends on
- [Group approximations](group-approx.md)
## Proof depends on
- [Chain approximations exist](chain-approx-exists.md), [properties](completed-maps-properties.md)
