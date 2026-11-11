---
article_id: af_0f19252ffe09ce926eb39b4e
declaration: def
origin: bridged
statement: formalized
lean: HSP.Corner.cutA
---

# The cut sets

Let $n\ge1$ and $s>0$. In the [round sphere](round-sphere.md) $S^n=\mathbb R^n\cup\{\infty\}$, the *cut sets* are, for $1\le m\le n$:
- $B_m=[-s,s]^{n-m+1}\times\{s\}^{m-1}\subseteq\mathbb R^n$;
- $Y_m=\{x\in B_m:|x_k|=s\text{ for some }k\le n-m+1\}$, the boundary of $B_m$ in the affine plane $\mathbb R^{n-m+1}\times\{s\}^{m-1}$;
- $Y_0=S^n$ and $A_m=\overline{Y_{m-1}\setminus B_m}$, the closure in $S^n$;

together with the points $y_\pm=(\pm s,s,\dots,s)$.

## Sources

- New: the cube-face flag replaces the ball and hemisphere flag of HS paper, Section 12. The cut sets depend only on $n$ and $s$.

## Depends on

- [The round sphere](round-sphere.md)
