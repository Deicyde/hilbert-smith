---
article_id: af_935a8f84cf2a6a851f88d17f
declaration: lemma
origin: background
statement: formalized
lean: HSP.ChainModels.boxHull_properties
---
# Box hull properties

Let $k\ge8$ and $h=4/k$. Call $X\subseteq\mathbb T^n$ *admissible* if $X$ is nonempty and each coordinate projection $X_j\subseteq\mathbb R/4\mathbb Z$ lies in some closed arc of length at most $1$. Let $X,Y\subseteq\mathbb T^n$ be admissible, with $\mathrm{Box}_k$ the [box hull](box-hull.md) and $J_j$ the shortest closed arcs containing the $X_j$.
1. If $X\subseteq Y$, then $\mathrm{Box}_k(X)\subseteq\mathrm{Box}_k(Y)$.
2. $|\mathrm{Box}_k(X)|$ lies in the closed $d_\infty$-neighbourhood of radius $h$ of $\prod_jJ_j$. Hence $\operatorname{diam}_\infty|\mathrm{Box}_k(X)|\le\operatorname{diam}_\infty X+2h$.
3. If $N_h(X)$, the closed $d_\infty$-neighbourhood of radius $h$ of $X$, is also admissible, then every cube whose closed cube meets $X$ lies in $\mathrm{Box}_k(N_h(X))$.

*Proof sketch.* Each statement is checked one coordinate at a time, and $d_\infty$ is the maximum over coordinates. Two facts are used.
- *Uniqueness.* For admissible $X$, $J_j$ and $A_j$ are unique. The closure of $X_j$ lies in an arc of length at most $1$, so its complement in the circle of length $4$ contains an open arc of length at least $3$; a shortest closed arc containing $X_j$ is the complement of a longest open arc in the complement of $X_j$, and since the circle has length $4$ there is exactly one open gap longer than $2$. So $J_j$ is unique, of length at most $1$. A grid arc covers $J_j$ exactly when its first vertex is at or before the start of $J_j$ and its last vertex at or after the end of $J_j$, both read in the lift of an arc of length less than $4$; the smallest one starts at the last grid point $4w/k$ at or before the start of $J_j$ and ends at the first grid point at or after its end. It has at most $k/4+2\le k-2$ edges for $k\ge8$, so it is a grid arc, and it is unique.
- *Cubes of a grid box.* If a cube $c=b_1\otimes\dots\otimes b_n$ has $|c|\subseteq|B|$ for a grid box $B=\bigotimes_jA_j$, then each $b_j$ is a cell of $A_j$. Indeed $|A_j|$ is the arc from $4w/k$ to $4(w+m)/k$ with $m\le k-2$, so the grid points it contains are exactly its vertices $[w],\dots,[w+m]$; a vertex in $|A_j|$ is one of these, and an edge whose closed realization lies in $|A_j|$ joins two consecutive vertices of $A_j$ through $|A_j|$, not through the complementary arc, which contains at least two edges, so it is one of $e_w,\dots,e_{w+m-1}$.

 (1) $X_j\subseteq Y_j$ gives $J_j(X)\subseteq J_j(Y)$, so the smallest grid arc covering $J_j(Y)$ covers $J_j(X)$. (2) The smallest grid arc covering $J_j$ overshoots each end of $J_j$ by less than $h$, and the length of $J_j$ is the circle diameter of $X_j$, which is at most $\operatorname{diam}_\infty X$. (3) A closed cube meeting $X$ has each coordinate projection inside the $h$-neighbourhood of $X_j$, which lies in $J_j(N_h(X))\subseteq|A_j(N_h(X))|$; so the closed cube lies in $|\mathrm{Box}_k(N_h(X))|$, and by the second fact the cube lies in $\mathrm{Box}_k(N_h(X))$.

**Remark (not formalized).** $|\mathrm{Box}_k(X)|$ need not lie near $X$ itself: for $n=2$ and $X=\{(0,0),(1,1)\}$, the point $(0,1)$ lies in the box at $d_\infty$-distance $1$ from $X$.

## Sources
- New.
## Depends on
- [The closed cube](cubical/grid-cube-realization.md)
- [Grid cubes](cubical/grid-cube.md)
- [Box hull](box-hull.md), [cubical torus grid](cubical/cubical-torus-grid.md), [grid boxes](grid-box.md)
