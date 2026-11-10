---
article_id: af_cc00bf3ad61bed3ce13ab45d
declaration: def
origin: bridged
---

# Tensoring with a permutation module

Let $X$ be a finite $G$-set with a bijection $\varepsilon_X:X\to\{0..|X|-1\}$, and enumerate $X\times\{1..n\}$ by $e^X_n(x,k)=\varepsilon_X(x)\,n+k\in\{1..|X|n\}$, as the [permutation tensor](../../categories/functors/tensor-permutation.md) of the asymptotic category does for $X=C_p$. The strict duality functor $\tau_X:\mathrm{Free}(\mathbb Q[G])\to\mathrm{Free}(\mathbb Q[G])$ sends $n$ to $|X|n$ and a morphism $u:n\to n'$ to the reindexing, by [bases of finite free sets](../../categories/asymptotic/free-set-basis.md), of the matrix $(1_X\otimes u)_{(y',c'),(y,c)}=\delta_{y'y}u_{c'c}$ on the free $G$-sets $X\times(G\times\{1..n\})$ and $X\times(G\times\{1..n'\})$ with the diagonal action, with the orbit representatives $(x,1,k)$. Explicitly, writing $(g,(x,k))$ for the basis element $(g,e^X_n(x,k))$,
$$\tau_X(u)_{(g',(x',k')),(g,(x,k))}=\begin{cases}u_{(g',k'),(g,k)}&\text{if }g'x'=gx,\\0&\text{otherwise.}\end{cases}$$

*Proof sketch.* The diagonal action is free because the action on $G\times\{1..n\}$ is. The orbit of $(y,g,k)$ contains exactly one representative, $g^{-1}(y,g,k)=(g^{-1}y,1,k)$. $1_X\otimes u$ is equivariant because $u$ is. $1_X\otimes-$ preserves identities, products and transposes, and so does [reindexing](../../categories/asymptotic/free-set-basis.md). The explicit formula is the reindexing along $(g,(x,k))\mapsto(gx,g,k)$.

**Remark (not formalized).** For $X=C_p=\{0..p-1\}$ with $G_i$ acting by $g\cdot c=\chi_i(g)+c$ and $\varepsilon_{C_p}$ the identity, $e^{C_p}_n$ is the permutation enumeration $e_n(c,k)=c\,n+k$ of the [permutation tensor](../../categories/functors/tensor-permutation.md), and $\tau_{C_p}(u)_{(g',(c',k')),(g,(c,k))}$ is $u_{(g',k'),(g,k)}$ if $\chi_i(g')+c'=\chi_i(g)+c$ and $0$ otherwise. This is that functor's matrix entry for entry, so forgetting labels commutes strictly with the two permutation tensors.

## Sources

- HS paper, Section 3
- New: the orthonormal form on $\mathbb Q[X]$ is the identity matrix, so $(1\otimes u)^T=1\otimes u^T$.

## Depends on

- [Permutation tensor](../../categories/functors/tensor-permutation.md)
- [Free category of a finite group](../../categories/asymptotic/free-category.md)
- [Bases of finite free G-sets](../../categories/asymptotic/free-set-basis.md)
- [Duality functor](../../l-theory/base/categories/duality-functor.md)
