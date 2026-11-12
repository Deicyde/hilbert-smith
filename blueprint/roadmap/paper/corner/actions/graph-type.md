---
article_id: af_eefcb5293d989a876c7b27c1
declaration: def
origin: bridged
statement: formalized
lean: HSP.Corner.IsGraphType
---

# Graph-type matrices

Let $X$ be a metric space with an isometric action $(c,x)\mapsto c\cdot x$ of $C_p=\mathbb Z/p$, written additively. Let $M,M'$ be finite based $\mathbb Q$-modules whose basis elements carry labels $\lambda_b\in X$. Fix $c\in C_p$ and $\delta\ge0$. A matrix $u:M\to M'$ has *graph type $c$ with bound $\delta$* if every nonzero entry $u_{b'b}$ satisfies $d(\lambda_{b'},c\cdot\lambda_b)\le\delta$. The definition does not need the action to be isometric, the bases to be finite, or $\delta\ge0$.

**Remark (not formalized).** For $X=T\times S^n$ as in the [standing data](../standing-data.md), with labels $\lambda_b=(t_b,z_b)$, this says $d_T(t_{b'},c\cdot t_b)\le\delta$ and $d_S(z_{b'},z_b)\le\delta$. Type $0$ with bound $\delta$ is the same as [propagation](../../categories/asymptotic/propagation.md) at most $\delta$.

## Sources

- HS paper, Section 9.
- New: the type is an element of $C_p$, and $X$ is any isometric $C_p$-space.

## Depends on

