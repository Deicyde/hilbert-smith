---
article_id: af_3298d3b8b0b48709f5231e48
declaration: def
origin: bridged
---

# Permutation tensor

Write $C_p=\{0,\dots,p-1\}$ additively. For $n\in\mathbb N$ the *permutation enumeration* is the bijection
$$e_n:C_p\times\{1..n\}\to\{1..p\,n\},\qquad e_n(c,k)=c\,n+k,$$
and for a basis element $(g,e_n(c,k))$ of $G_i\times\{1..p\,n\}$ we write $(g,c,k)$.

$\tau\otimes-:\mathcal A_{\mathbf G}(X)\to\mathcal A_{\mathbf G}(X)$ is the strict duality functor defined as follows. It sends $(n_i,x_i)$ to $(p\,n_i,x'_i)$ with $x'_i(e_{n_i}(c,k))=x_i(k)$. It sends $[u]$, with $u_i:(n_i,x_i)\to(n'_i,x''_i)$, to $[\tau u]$, where
$$(\tau u_i)_{(g,c',k'),(h,c,k)}=\begin{cases}(u_i)_{(g,k'),(h,k)}&\text{if }\chi_i(g)+c'=\chi_i(h)+c,\\0&\text{otherwise,}\end{cases}$$
rows enumerated by $e_{n'_i}$ and columns by $e_{n_i}$.

*Proof sketch.* $e_n$ is a bijection because $(c,k)\mapsto c\,n+k$ is division with remainder. $\tau u_i$ is equivariant because the condition $\chi_i(g)+c'=\chi_i(h)+c$ and $u_i$ are invariant under $(g,h)\mapsto(ag,ah)$. The basis element $(g,c,k)$ has the label $\chi_i(g)x_i(k)$, the label of $(g,k)$, so $\operatorname{prop}(\tau u_i)\le\operatorname{prop}(u_i)$. In $(\tau v_i\,\tau u_i)$, for each middle $(h,k')$ exactly one $c'$ satisfies the condition, which gives $\tau(v_iu_i)$. Identities go to identities, $\tau$ is $\mathbb Q$-linear, and the condition is symmetric, so $\tau(u_i^{T})=(\tau u_i)^{T}$.

**Remark (not formalized).** Under the equivariant bijection $(g,c,k)\mapsto(\chi_i(g)+c,(g,k))$ onto $C_p\times(G_i\times\{1..n_i\})$ with the diagonal action, $\tau u_i$ becomes $\mathrm{id}_{\mathbb Q[C_p]}\otimes u_i$. When $\chi_i$ is onto with kernel $P_i$, this is tensoring with the permutation module $\mathbb Q[G_i/P_i]$. The functors on point categories that must agree with $\tau\otimes-$ strictly ([tensoring with a permutation module](../../signatures/point-functors/permutation-tensor.md) for $C_p$, and [the permutation tensor on tails](../../signatures/point-functors/tail-permutation-functor.md)) use the same $e_n$.

## Sources

- HS paper, Section 4

## Depends on

- [Asymptotic duality](../asymptotic/asymptotic-duality.md)
