---
article_id: af_cc00bf3ad61bed3ce13ab45d
declaration: def
origin: bridged
---

# Tensoring with a permutation module

Let $X$ be a finite $G$-set, given with an enumeration of $X\times\{1..n\}$ by $\{1..|X|n\}$ for every $n$. The strict duality functor $\tau_X:\mathrm{Free}(\mathbb Q[G])\to\mathrm{Free}(\mathbb Q[G])$ sends $n$ to $|X|n$ and a morphism $u:n\to n'$ to the reindexing, by [bases of finite free sets](../../categories/asymptotic/free-set-basis.md), of the matrix $(1_X\otimes u)_{(y',c'),(y,c)}=\delta_{y'y}u_{c'c}$ on the free $G$-sets $X\times(G\times\{1..n\})$ and $X\times(G\times\{1..n'\})$ with the diagonal action, with the orbit representatives $(x,1,k)$. Explicitly,
$$\tau_X(u)_{(g',(x',k')),(g,(x,k))}=\begin{cases}u_{(g',k'),(g,k)}&\text{if }g'x'=gx,\\0&\text{otherwise.}\end{cases}$$

*Proof sketch.* The diagonal action is free because the action on $G\times\{1..n\}$ is. The orbit of $(y,g,k)$ contains exactly one representative, $g^{-1}(y,g,k)=(g^{-1}y,1,k)$. $1_X\otimes u$ is equivariant because $u$ is. $1_X\otimes-$ preserves identities, products and transposes, and so does [reindexing](../../categories/asymptotic/free-set-basis.md). The explicit formula is the reindexing along $(g,(x,k))\mapsto(gx,g,k)$.

**Remark (not formalized).** For $X=C_p$ with $G_i$ acting by $g\cdot c=\chi_i(g)+c$, and the enumeration of $C_p\times\{1..n\}$ fixed in the [permutation tensor](../../categories/functors/tensor-permutation.md) of the asymptotic category, $\tau_{C_p}(u)_{(g',(c',k')),(g,(c,k))}$ is $u_{(g',k'),(g,k)}$ if $\chi_i(g')+c'=\chi_i(g)+c$ and $0$ otherwise, which is that functor's formula.

## Sources

- HS paper, Section 3
- New: the orthonormal form on $\mathbb Q[X]$ is the identity matrix, so $(1\otimes u)^T=1\otimes u^T$.

## Depends on

- [Free category of a finite group](../../categories/asymptotic/free-category.md)
- [Bases of finite free G-sets](../../categories/asymptotic/free-set-basis.md)
- [Duality functor](../../l-theory/base/categories/duality-functor.md)
