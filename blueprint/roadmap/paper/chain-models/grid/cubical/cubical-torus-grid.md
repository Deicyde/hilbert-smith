---
article_id: af_d8f03e9f38409b85e59b3d09
declaration: def
origin: background
statement: formalized
lean: HSP.ChainModels.gridComplex
---

# Cubical torus grid

For $k,n\in\mathbb N$, the *grid complex* is $C(k)=S_k^{\otimes n}$, the iterated [tensor product of based complexes](../based-complex-tensor.md) $(\cdots((\mathbb 1\otimes S_k)\otimes S_k)\otimes\cdots)\otimes S_k$ with $n$ factors the [circle complex](circle-complex.md) $S_k$, which [vanishes in negative degrees](circle-dim-neg.md), starting from the [unit complex](unit-complex.md) $\mathbb 1$ ($\mathbb Q$ in degree $0$); tensoring with $\mathbb 1$ on the left changes neither the complex nor its bases, so this is $(\cdots(S_k\otimes S_k)\otimes\cdots)\otimes S_k$, with differential $d\otimes1+(-1)^p1\otimes d$ on $A_p\otimes B_q$. The tensor of basis elements $x\otimes y$ is a basis element, with no sign. It is a complex in the [category of based $\mathbb Q$-vector spaces](../../../l-theory/localization/products/bookkeeping/based-category.md). Its cells (the cubes), their closed cubes in the torus, its augmentation and its fundamental chain are defined in their own articles.

*Bases.* Every finite based complex of this chapter is a complex in the category $\mathbb Q$ of based vector spaces, read through a fixed enumeration of its cells: in each degree $r$ the chain object is $\mathbb Q^{d_r}$, $d_r$ the number of cells of degree $r$, and the $i$-th cell is the basis vector $e_i$, its dual the dual basis vector $e_i^*$. The cells are enumerated in the order in which they are written: $[0],\dots,[k-1]$ and $e_0,\dots,e_{k-1}$ for $S_k$, and likewise for every other complex of the chapter given by a list of cells (the arcs and their boundaries, the point, the cells of $\mathbb{CP}^2$). Tensor products of complexes are the tensor product of based complexes, built on the tensor product of based vector spaces: the summands $A_p\boxtimes B_q$ of degree $r$ are concatenated in increasing order of $p$, and inside a summand $x_i\otimes y_j$ is the basis vector $e_{(i-1)b+j}$, $b$ the number of cells $y$ of degree $q$. Labels of cells are labels of these basis vectors.

## Sources

- [Massey 1980, cubical singular theory](../../../../../sources/paper/massey-1980.md); product cell structures [U]
- New: the torus grid as an $n$-fold tensor power of a circle.

## Depends on

- [The category of based ℚ-vector spaces](../../../l-theory/localization/products/bookkeeping/based-category.md)

## Proof depends on

- [The circle complex](circle-complex.md)
- [The circle complex vanishes in negative degrees](circle-dim-neg.md)
- [The unit complex](unit-complex.md)
- [Tensor product of based complexes](../based-complex-tensor.md)
