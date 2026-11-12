---
article_id: af_2a6cd79e8db1763ac7bcdbba
declaration: def
origin: background
statement: formalized
lean: HSP.ChainModels.boxHull
---
# Box hull

Let $k\ge8$ and $X\subseteq\mathbb T^n$, with coordinate projections $X_j\subseteq\mathbb R/4\mathbb Z$. A closed arc is the image of an interval $[a,a+\ell]$, $\ell\ge0$, of length $\ell$. Let $J_j$ be a shortest closed arc containing $X_j$, and $A_j$ a smallest [grid arc](grid-box.md) with $J_j\subseteq|A_j|$ (a fixed choice in each case, the whole circle and the arc $[0]$ if there is none). Then $\mathrm{Box}_k(X)=\bigotimes_jA_j$.

**Remark (not formalized).** The hull is used when $X$ is nonempty and each $X_j$ lies in some closed arc of length at most $1$. Then $J_j$ is unique, because the complement of $X_j$ has exactly one gap longer than $2$, and so is $A_j$.

## Sources
- New.
## Depends on
- [Grid cubes](cubical/grid-cube.md)
- [Grid boxes](grid-box.md)
