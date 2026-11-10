---
article_id: af_3298d3b8b0b48709f5231e48
declaration: def
origin: bridged
---

# Permutation tensor

$\tau\otimes-:\mathcal A_{\mathbf G}(X)\to\mathcal A_{\mathbf G}(X)$ is the strict duality functor defined as follows. It sends $(n_i,x_i)$ to $(p\,n_i,x'_i)$, where the generators $\{1..p\,n_i\}$ are identified with $C_p\times\{1..n_i\}$ in a fixed order and $x'_i(c,k)=x_i(k)$. It sends $[u]$ to $[\tau u]$, where
$$(\tau u_i)_{(g,c',k'),(h,c,k)}=\begin{cases}(u_i)_{(g,k'),(h,k)}&\text{if }\chi_i(g)c'=\chi_i(h)c,\\0&\text{otherwise.}\end{cases}$$

*Proof sketch.* $\tau u_i$ is equivariant because the condition $\chi_i(g)c'=\chi_i(h)c$ and $u_i$ are invariant under $(g,h)\mapsto(ag,ah)$. The basis element $(g,(c,k))$ has the label $\chi_i(g)x_i(k)$, the label of $(g,k)$, so $\operatorname{prop}(\tau u_i)\le\operatorname{prop}(u_i)$. In $(\tau v_i\,\tau u_i)$, for each middle $(h,k')$ exactly one $c'$ satisfies the condition, which gives $\tau(v_iu_i)$. Identities go to identities, $\tau$ is $\mathbb Q$-linear, and the condition is symmetric, so $\tau(u_i^{T})=(\tau u_i)^{T}$.

**Remark (not formalized).** Under the equivariant bijection $(g,(c,k))\mapsto(\chi_i(g)c,(g,k))$ onto $C_p\times(G_i\times\{1..n_i\})$ with the diagonal action, $\tau u_i$ becomes $\mathrm{id}_{\mathbb Q[C_p]}\otimes u_i$. When $\chi_i$ is onto with kernel $P_i$, this is tensoring with the permutation module $\mathbb Q[G_i/P_i]$.

## Sources

- HS paper, Section 4

## Depends on

- [Asymptotic duality](../asymptotic/asymptotic-duality.md)
