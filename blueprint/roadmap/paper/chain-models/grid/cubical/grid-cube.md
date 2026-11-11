---
article_id: af_a515676aae4bb68307d4da82
declaration: abbrev
origin: background
statement: formalized
lean: HSP.ChainModels.GridCube
---

# Grid cubes

A *cube* of the cubical torus grid is $c=(w,S)$ with $w\in(\mathbb Z/k)^n$ and $S\subseteq\{1,\dots,n\}$, written $c=b_1\otimes\dots\otimes b_n$ with $b_j=e_{w_j}$ if $j\in S$ and $b_j=[w_j]$ otherwise, cells of the [circle complex](circle-complex.md). Its dimension is $\dim c=|S|$. The closed cube $|c|\subseteq\mathbb T^n$ is the product of the realizations of the $b_j$, and its center $x_c$ has coordinates $4w_j/k$, plus $2/k$ if $j\in S$. The closed star $\operatorname{st}(c)$ is the union of the closed cubes containing $|c|$. The two faces of $c$ in a coordinate $j\in S$ replace $e_{w_j}$ by $[w_j]$ and by $[w_j+1]$, and a *subcomplex* is a set of cubes closed under taking faces.

## Sources

- New: companion of the cubical torus grid.

## Depends on

- [The circle complex](circle-complex.md)
- [The torus](../torus.md)
