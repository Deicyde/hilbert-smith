---
article_id: af_d8f03e9f38409b85e59b3d09
declaration: def
origin: background
---

# Cubical torus grid

Fix $n\ge1$. Let $\mathbb T^n=(\mathbb R/4\mathbb Z)^n$. It carries two metrics: $d_\infty$, the maximum of the circle distances, and $d_2$, the quotient Euclidean metric, so that $d_\infty\le d_2\le\sqrt n\,d_\infty$. For $X\subseteq\mathbb T^n$ and $r\ge0$, $N_r(X)$ is the closed $d_\infty$-neighbourhood of $X$ of radius $r$. For an integer $k\ge3$ put $h=4/k$.

The *circle complex* $S_k$ is defined as follows. $S_{k,0}$ has basis $[w]$ and $S_{k,1}$ has basis $e_w$, both indexed by $w\in\mathbb Z/k$. The differential is $de_w=[w+1]-[w]$, and the augmentation is $\varepsilon[w]=1$. The realization of $[w]$ is the point $4w/k$, and the realization of $e_w$ is the arc from $4w/k$ to $4(w+1)/k$.

The *grid complex* is $C(k)=S_k^{\otimes n}$, the iterated tensor product $(\cdots(S_k\otimes S_k)\otimes\cdots)\otimes S_k$ with differential $d\otimes1+(-1)^p1\otimes d$ on $A_p\otimes B_q$, and augmentation $\varepsilon^{\otimes n}$. The tensor of basis elements $x\otimes y$ is a basis element, with no sign. Its basis consists of the *cubes* $c=(w,S)$ with $w\in(\mathbb Z/k)^n$ and $S\subseteq\{1,\dots,n\}$. Here $c=b_1\otimes\dots\otimes b_n$, where $b_j=e_{w_j}$ if $j\in S$ and $b_j=[w_j]$ otherwise, and $\dim c=|S|$. The closed cube $|c|\subseteq\mathbb T^n$ is the product of the realizations, and its center is $x_c$. The closed star $\operatorname{st}(c)$ is the union of the closed cubes containing $|c|$.

*Bases.* Every finite based complex of this chapter is a complex in the category $\mathbb Q$ of [based vector spaces](../../l-theory/localization/products/based-vector-spaces.md), read through a fixed enumeration of its cells: in each degree $r$ the chain object is $\mathbb Q^{d_r}$, $d_r$ the number of cells of degree $r$, and the $i$-th cell is the basis vector $e_i$, its dual the dual basis vector $e_i^*$. The cells are enumerated in the order in which they are written: $[0],\dots,[k-1]$ and $e_0,\dots,e_{k-1}$ for $S_k$, and likewise for every other complex of the chapter given by a list of cells (the arcs and their boundaries, the point, the cells of $\mathbb{CP}^2$). Tensor products of complexes are the [tensor product of complexes](../../l-theory/localization/products/complex-product.md) for the pairing [tensor product of based vector spaces](../../l-theory/localization/products/based-tensor.md): the summands $A_p\boxtimes B_q$ of degree $r$ are concatenated in increasing order of $p$, and inside a summand $x_i\otimes y_j$ is the basis vector $e_{(i-1)b+j}$, $b$ the number of cells $y$ of degree $q$. Labels of cells are labels of these basis vectors.

The *fundamental chain* is $z(k)=\bigotimes_j\sum_w e_w$. A *subcomplex* is the span of a set of cubes that is closed under taking faces.

## Sources

- [Massey 1980, cubical singular theory](../../../../sources/paper/massey-1980.md); product cell structures [U]
- New: the torus grid as an $n$-fold tensor power of a circle.

## Depends on

- [Based vector spaces](../../l-theory/localization/products/based-vector-spaces.md), [tensor product of complexes](../../l-theory/localization/products/complex-product.md), [tensor product of based vector spaces](../../l-theory/localization/products/based-tensor.md)
