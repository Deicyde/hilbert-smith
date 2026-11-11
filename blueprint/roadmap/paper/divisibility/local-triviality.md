---
article_id: af_cd693c188b7f6f80e2069c55
declaration: lemma
origin: bridged
---

# Local triviality

Let $\mathbf G$ be a group sequence, $X$ a compact metric space with an isometric $C_p$-action, and $S\subseteq X$ closed and invariant. Suppose there is a continuous map $c:S\to C_p$ with $c(gx)=g+c(x)$ for $g\in C_p$. Then $\nu_S=0$ on $\mathbb L_k(\mathcal A_S)$ for all $k$, with [$\nu$](permutation-nu.md) as defined on the support Mayer-Vietoris functor.

*Proof sketch.*
1. The sheets $c^{-1}(j)$, $j\in C_p$, are compact and pairwise disjoint, so any two are at distance at least some $\delta>0$. A point within $\delta/3$ of $S$ is within $\delta/3$ of exactly one sheet; call its index $\bar c$. Because the action is isometric and $c$ is equivariant, $\bar c(gy)=g+\bar c(y)$. Two points within $\delta/3$ of $S$ and of each other have the same $\bar c$, since otherwise two sheets would be closer than $\delta$.
2. For $M=(n_i,x_i)$ in $\mathcal A_S$ there is $i_0$ with every $x_i(k)$, $i\ge i_0$, within $\delta/3$ of $S$. Since $S$ is invariant and the action isometric, so is every label $\lambda_i(g,k)=\chi_i(g)\cdot x_i(k)$.
3. By the [permutation tensor](../categories/functors/tensor-permutation.md), $\tau\otimes M$ has the basis elements $(g,c',k)=(g,e_{n_i}(c',k))$, $(g,c',k)\in G_i\times C_p\times\{1..n_i\}$, with labels $\lambda_i(g,k)$. Write $M^{\oplus p}$ for the $p$-fold sum, with its copies indexed by $C_p$, so its basis elements are $(g,k)$ in copy $j\in C_p$, with labels $\lambda_i(g,k)$. For $i\ge i_0$ let $\theta_{M,i}$ send $(g,c',k)$ to $(g,k)$ in copy $\chi_i(g)+c'-\bar c(\lambda_i(g,k))$; for $i<i_0$ let it send $(g,c',k)$ to $(g,k)$ in copy $c'$. For fixed $(g,k)$ both are bijections in $c'$, so $\theta_{M,i}$ is a bijection of bases. It is equivariant: for $a\in G_i$ (the $G_i$ are written multiplicatively), $a(g,c',k)=(ag,c',k)$ goes to copy $\chi_i(a)+\chi_i(g)+c'-\bar c(\chi_i(a)\cdot\lambda_i(g,k))$, which is the same copy by step 1. It preserves labels. So its permutation matrices form an isomorphism $\theta_M:\tau\otimes M\to M^{\oplus p}$ in $\mathcal A_S$ of propagation $0$ with $\theta_M^*=\theta_M^{-1}$.
4. (Naturality.) Let $u:M\to M'$ in $\mathcal A_S$. For $i$ large, $\operatorname{prop}(u_i)<\delta/3$ and all labels of $M$ and $M'$ are within $\delta/3$ of $S$. Then a nonzero entry $(u_i)_{(g',k'),(h,k)}$ joins labels with the same $\bar c$ by step 1, so the condition $\chi_i(g')+c'=\chi_i(h)+c$ of $\tau u_i$ says exactly that $(g',c',k')$ and $(h,c,k)$ go to the same copy. Hence $\theta_{M'}(\tau u)=u^{\oplus p}\theta_M$ modulo eventual equality, and $\theta$ is a natural isomorphism $\tau_S\cong\mathrm{id}^{\oplus p}$ of strict duality functors on $\mathcal A_S$, unitary because $\theta_M^*=\theta_M^{-1}$.
5. By [unitary invariance on ultimate L](../l-theory/ultimate/groups/unitary-invariance.md), $(\tau_S)_*=(\mathrm{id}^{\oplus p})_*$, which is $p\cdot\mathrm{id}$ by [additivity on ultimate L](../l-theory/ultimate/groups/sum-additivity.md) and [identity on ultimate L](../l-theory/ultimate/groups/induced-map-id.md). So $\nu_S=0$.

## Sources

- HS paper, Section 4 (Local triviality).
- New: sheet index taken near $S$ itself, with no trivializing neighborhood.

## Depends on

- [The endomorphism $\nu$](permutation-nu.md)

## Proof depends on

- [Permutation tensor](../categories/functors/tensor-permutation.md)
- [Support subcategory](../categories/supports/support-subcategory.md)
- [Unitary natural isomorphism](../l-theory/base/categories/unitary-isomorphism.md)
- [Sums of functors](../l-theory/base/groups/sum-of-functors.md)
- [Unitary invariance on ultimate L](../l-theory/ultimate/groups/unitary-invariance.md)
- [Additivity on ultimate L](../l-theory/ultimate/groups/sum-additivity.md)
- [Identity on ultimate L](../l-theory/ultimate/groups/induced-map-id.md)
