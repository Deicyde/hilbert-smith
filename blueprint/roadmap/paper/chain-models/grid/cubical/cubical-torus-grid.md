---
article_id: af_d8f03e9f38409b85e59b3d09
declaration: def
origin: background
statement: formalized
lean: HSP.ChainModels.gridComplex
---

# Cubical torus grid

Fix $n\in\mathbb N$, and let $\mathbb T^n=(\mathbb R/4\mathbb Z)^n$, its distance $d_\infty$, and the neighbourhoods $N_r(X)$ be those of [the torus](../torus.md). For an integer $k\ge1$ put $h=4/k$. The complexes below are defined for every $k\in\mathbb N$; $k\ge1$ is needed only for the mesh $h$ and the faces.

The [circle complex](circle-complex.md) $S_k$ has basis $[w]$ in degree $0$ and $e_w$ in degree $1$, $w\in\mathbb Z/k$, with $de_w=[w+1]-[w]$ and [augmentation](circle-aug.md) $\varepsilon[w]=1$.

The *grid complex* is $C(k)=S_k^{\otimes n}$, the iterated [tensor product of based complexes](../based-complex-tensor.md) $(\cdots((\mathbb 1\otimes S_k)\otimes S_k)\otimes\cdots)\otimes S_k$ with $n$ factors $S_k$, starting from the [unit complex](unit-complex.md) $\mathbb 1$ ($\mathbb Q$ in degree $0$); tensoring with $\mathbb 1$ on the left changes neither the complex nor its bases, so this is $(\cdots(S_k\otimes S_k)\otimes\cdots)\otimes S_k$, with differential $d\otimes1+(-1)^p1\otimes d$ on $A_p\otimes B_q$. Its augmentation is $\varepsilon^{\otimes n}$, the Kronecker product of the augmentations on $C(k)_0$. The tensor of basis elements $x\otimes y$ is a basis element, with no sign. Its basis consists of the [cubes](grid-cube.md) $c=(w,S)$ with $w\in(\mathbb Z/k)^n$ and $S\subseteq\{1,\dots,n\}$. Here $c=b_1\otimes\dots\otimes b_n$, where $b_j=e_{w_j}$ if $j\in S$ and $b_j=[w_j]$ otherwise, and $\dim c=|S|$. The closed cube $|c|\subseteq\mathbb T^n$ is the product of the realizations, and its center $x_c$ has coordinates $4w_j/k$, plus $2/k$ if $j\in S$. The closed star $\operatorname{st}(c)$ is the union of the closed cubes containing $|c|$.

*Bases.* Every finite based complex of this chapter is a complex in the category $\mathbb Q$ of [based vector spaces](../../../l-theory/localization/products/based-vector-spaces.md), read through a fixed enumeration of its cells: in each degree $r$ the chain object is $\mathbb Q^{d_r}$, $d_r$ the number of cells of degree $r$, and the $i$-th cell is the basis vector $e_i$, its dual the dual basis vector $e_i^*$. The cells are enumerated in the order in which they are written: $[0],\dots,[k-1]$ and $e_0,\dots,e_{k-1}$ for $S_k$, and likewise for every other complex of the chapter given by a list of cells (the arcs and their boundaries, the point, the cells of $\mathbb{CP}^2$). Tensor products of complexes are the [tensor product of based complexes](../based-complex-tensor.md), built on the [tensor product of based vector spaces](../../../l-theory/localization/products/based-tensor.md): the summands $A_p\boxtimes B_q$ of degree $r$ are concatenated in increasing order of $p$, and inside a summand $x_i\otimes y_j$ is the basis vector $e_{(i-1)b+j}$, $b$ the number of cells $y$ of degree $q$. Labels of cells are labels of these basis vectors.

The *fundamental chain* is $z(k)=\bigotimes_j\sum_w e_w\in C(k)_n$. The two faces of a cube $c$ in a coordinate $j\in S$ replace $e_{w_j}$ by $[w_j]$ and by $[w_j+1]$. A *subcomplex* is the span of a set of cubes that is closed under taking faces.

## Sources

- [Massey 1980, cubical singular theory](../../../../../sources/paper/massey-1980.md); product cell structures [U]
- New: the torus grid as an $n$-fold tensor power of a circle.

## Depends on

- [The circle complex](circle-complex.md), [the circle complex vanishes in negative degrees](circle-dim-neg.md), [the unit complex](unit-complex.md), [grid cubes](grid-cube.md)
- [The torus](../torus.md)
- [Based vector spaces](../../../l-theory/localization/products/based-vector-spaces.md), [tensor product of based vector spaces](../../../l-theory/localization/products/based-tensor.md), [tensor product of based complexes](../based-complex-tensor.md)
