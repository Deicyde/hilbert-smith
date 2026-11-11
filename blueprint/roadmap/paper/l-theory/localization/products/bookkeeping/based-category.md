---
article_id: af_74edb172ee799d79756f4872
declaration: structure
origin: background
statement: formalized
lean: HSP.FreeQ
---

# The category of based ℚ-vector spaces

The category $\mathbb Q$ of based vector spaces is defined as follows.
- Its objects are the natural numbers $d$, written $\mathbb Q^d$.
- A morphism $\mathbb Q^d\to\mathbb Q^{d'}$ is a $d'\times d$ rational matrix; a morphism is read as its matrix and a matrix as a morphism, and these two passages are mutually inverse.
- Composition is the matrix product, $g\circ f=gf$, and the identity of $\mathbb Q^d$ is the identity matrix.
- Sums and rational multiples of morphisms are taken entrywise, the zero morphism is the zero matrix, and composition is bilinear; so $\mathbb Q$ is a $\mathbb Q$-linear additive category.
- The block inclusions and projections make $\mathbb Q^{d+d'}$ a biproduct of $\mathbb Q^d$ and $\mathbb Q^{d'}$, and $\mathbb Q^0$ is a zero object; hence $\mathbb Q$ has finite biproducts.

*Proof sketch.* (Proof obligations.) Associativity and unitality are those of the matrix product, and its distributivity and compatibility with scalars give bilinearity. For the biproduct, with $\iota_1=\binom{1}{0}$, $\iota_2=\binom{0}{1}$, $\pi_1=(1\ 0)$, $\pi_2=(0\ 1)$, one has $\pi_i\iota_j=\delta_{ij}$ and $\iota_1\pi_1+\iota_2\pi_2=1$. The only $0\times0$ matrix is zero, so $1=0$ on $\mathbb Q^0$.

## Sources

- [Ranicki 1992, §1, free modules with the transpose duality](../../../../../../sources/paper/ranicki-1992.md) [U]

## Depends on
