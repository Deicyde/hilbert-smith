---
article_id: af_935a8f84cf2a6a851f88d17f
declaration: lemma
origin: background
---
# Box hull properties

Let $X,Y\subseteq\mathbb T^n$ satisfy the hypotheses of the [box hull](box-hull.md), with shortest arcs $J_j$ for $X$, and let $h=4/k$.
1. If $X\subseteq Y$, then $\mathrm{Box}_k(X)\subseteq\mathrm{Box}_k(Y)$.
2. $|\mathrm{Box}_k(X)|$ lies in the closed $d_\infty$-neighbourhood of radius $h$ of $\prod_jJ_j$. Hence $\operatorname{diam}_\infty|\mathrm{Box}_k(X)|\le\operatorname{diam}_\infty X+2h$.
3. If $N_h(X)$ also satisfies the hypotheses, then every cube whose closed cube meets $X$ lies in $\mathrm{Box}_k(N_h(X))$.

*Proof sketch.* Each statement is checked one coordinate at a time, and $d_\infty$ is the maximum over coordinates. (1) $X_j\subseteq Y_j$ gives $J_j(X)\subseteq J_j(Y)$, so the smallest grid arc covering $J_j(Y)$ covers $J_j(X)$. (2) The smallest grid arc covering $J_j$ overshoots each end of $J_j$ by less than $h$, and the length of $J_j$ is the circle diameter of $X_j$, which is at most $\operatorname{diam}_\infty X$. (3) A closed cube meeting $X$ has each coordinate projection inside the $h$-neighbourhood of $X_j$, which lies in $J_j(N_h(X))$.

**Remark (not formalized).** $|\mathrm{Box}_k(X)|$ need not lie near $X$ itself: for $n=2$ and $X=\{(0,0),(1,1)\}$, the point $(0,1)$ lies in the box at $d_\infty$-distance $1$ from $X$.

## Sources
- New.
## Depends on
- [Box hull](box-hull.md), [cubical torus grid](cubical-torus-grid.md)
