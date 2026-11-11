---
article_id: af_f828bfdd9807276fdcb0ae3c
declaration: def
origin: background
statement: formalized
lean: HSP.Bounded.sumIsoIter
---

# Bounded extension of a sum of functors

Let $(F,\xi),(G,\zeta):\mathcal A\to\mathcal B$ be duality functors and $F\oplus G$ their [sum](../../base/categories/sums/duality-functor-sum.md). For $j\ge0$ there is a unitary natural isomorphism
$$\sigma_j:C_{\mathbb Z^j}(F\oplus G)\cong C_{\mathbb Z^j}F\oplus C_{\mathbb Z^j}G$$
of duality functors $C_{\mathbb Z^j}\mathcal A\to C_{\mathbb Z^j}\mathcal B$: $\sigma_0$ is the identity, and $\sigma_{j+1}$ has at $M=(M_n)_n$ the components into the two summands given by the diagonal matrices of propagation $0$ with entries $\pi\,(\sigma_j)_{M_n}$ and $\pi'\,(\sigma_j)_{M_n}$, where $\pi,\pi'$ are the projections of $C_{\mathbb Z^j}F(M_n)\oplus C_{\mathbb Z^j}G(M_n)$, in [The bounded category](../../bounded/categories/bounded-category.md) ([diagonal morphisms](../../bounded/categories/bounded-diag.md)).

*Proof sketch.* (Proof obligations, by induction on $j$; write $\sigma=\sigma_j$.) The inverse of $\sigma_{j+1}$ has components the diagonal matrices with entries $\sigma_{M_n}^{-1}\iota$ and $\sigma_{M_n}^{-1}\iota'$ on the two summands; both composites are diagonal with entries $\sigma(\pi\iota+\pi'\iota')\sigma^{-1}=\mathrm{id}$ and $\pi\sigma\sigma^{-1}\iota=\mathrm{id}$, $\pi'\sigma\sigma^{-1}\iota=0$, and so on. Both functors apply their entries entrywise, so naturality of $\sigma_{j+1}$ is naturality of $\sigma$ entrywise, followed by $\pi$ or $\pi'$. For unitarity, by the unfolding of the duality isomorphism of a sum, $\sigma_{j+1}^*\,\xi^{\oplus}\,\sigma_{j+1}$ is the diagonal matrix with entries $(\pi\sigma)^*\xi^{(j)}(\pi\sigma)+(\pi'\sigma)^*\zeta^{(j)}(\pi'\sigma)=\sigma^*\xi^{F\oplus G,(j)}\sigma$, which is the duality isomorphism of $C_{\mathbb Z^j}(F\oplus G)$ at $M_n$ because $\sigma$ is unitary.

## Sources

- New: levelwise.

## Depends on

- [Sum of duality functors](../../base/categories/sums/duality-functor-sum.md)
- [Unitary natural isomorphism](../../base/categories/unitary-isomorphism.md)
- [Bounded extension of a duality functor](../../bounded/categories/bounded-functor.md)
- [Iterated bounded extension](../../bounded/categories/bounded-functor-iter.md)
- [Diagonal morphisms of $C_\mathbb Z(A)$](../../bounded/categories/bounded-diag.md)
- [The bounded category](../../bounded/categories/bounded-category.md)
