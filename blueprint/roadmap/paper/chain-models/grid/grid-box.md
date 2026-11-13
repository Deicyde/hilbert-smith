---
article_id: af_eb59b625d30d1dcccf58d353
declaration: abbrev
origin: background
statement: formalized
lean: HSP.ChainModels.GridBox
---
# Grid boxes

A *grid arc* of $S_k$ is the subcomplex spanned by $[w],\dots,[w+m]$ and $e_w,\dots,e_{w+m-1}$, where $0\le m\le\max(k-2,0)$. Its realization is the arc $|A|$ from $4w/k$ to $4(w+m)/k$. Indices of cells are taken modulo $k$. A *grid box* is a tensor product $B=A_1\otimes\dots\otimes A_n\subseteq C(k)$ of grid arcs. It is spanned by the cubes $c=b_1\otimes\dots\otimes b_n$ with each $b_j$ a cell of $A_j$, and its realization is $|B|=\prod_j|A_j|$.

**Remark (not formalized).** These are exactly the cubes $c$ with $|c|\subseteq|B|$, since $m\le k-2$ when $k\ge2$.

## Sources
- New.
## Depends on

## Proof depends on

- [Grid cubes](cubical/grid-cube.md)
- [The torus](torus.md)
