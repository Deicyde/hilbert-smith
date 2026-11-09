---
declaration: def
origin: bridged
---

# Graph-type matrices

Let $X$ be a metric space with an isometric $C_p$-action. Let $M,M'$ be finite based $\mathbb Q$-modules whose basis elements carry labels $x_b\in X$. Fix $c\in C_p$ and $\delta\ge0$. A matrix $u:M\to M'$ has *graph type $c$ with bound $\delta$* if every nonzero entry $u_{b'b}$ satisfies $d(x_{b'},c\,x_b)\le\delta$.

For $X=T\times S^n$ with the maximum metric and $C_p$ acting on $T$, this says $d_T(t_{b'},c\,t_b)\le\delta$ and $d(z_{b'},z_b)\le\delta$. Type $1$ with bound $\delta$ is the same as propagation at most $\delta$.

## Sources

- HS paper, Section 9.
- New: the type is an element of $C_p$, and $X$ is any isometric $C_p$-space.

## Depends on

- [Standing data](standing-data.md)
- [Propagation](../categories/propagation.md)
