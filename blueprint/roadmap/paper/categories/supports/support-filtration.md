---
article_id: af_1f1ed0012a090acf98ecfb5f
declaration: def
origin: bridged
---

# Support filtration

Let $S'\subset S\subset X$ be closed and invariant. Then $\mathcal A_{S'}\subset\mathcal A_S$ is an [involution-invariant Karoubi filtration](../../l-theory/base/categories/karoubi-filtration.md), with the following chosen decompositions. Those of $M=(n_i,x_i)\in\mathcal A_S$ are indexed by the null sequences $r=(r_i)$ of nonnegative reals. For each such $r$, $M=M_{\le r}\oplus M_{>r}$, where $M_{\le r}$ keeps the indices $k$ with $x_i(k)\in\overline N_{r_i}(S')$ (the closed $r_i$-thickening), $M_{>r}$ keeps the rest, and the inclusions and projections are coordinate matrices with $\iota^{T}=\pi$. The case $S=X$ gives $\mathcal A_{S'}\subset\mathcal A_{\mathbf G}(X)$.

*Proof sketch.*
1. $\mathcal A_{S'}$ is a full additive subcategory of $\mathcal A_S$ closed under $M^*=M$.
2. $M_{\le r}$ is $S'$-supported because $r_i\to0$, and both pieces are $S$-supported because they are sub-objects of $M$. The coordinate matrices have propagation $0$ and satisfy the splitting identities.
3. Pointwise $r\le r'$ gives $M_{\le r}\subset M_{\le r'}$, so the projections are ordered. The pointwise maximum of two null sequences is null, so the family is directed.
4. (Factorization.) Given $g:V\to M$ with $V\in\mathcal A_{S'}$, the [support ideal](support-ideal.md) gives a null $r$ bounding the distance to $S'$ of the row labels of the nonzero entries of $g_i$. Then $g=\iota\pi g$. Maps $M\to V$ are handled by transposing.
5. (Duality.) $M^*=M$, and the projection of each split is self-transpose because $\iota^{T}=\pi$.

**Remark (not formalized).** The definition asks for no sum axiom; compatibility with sums holds in the cofinal sense ([filtrations are compatible with sums](../../l-theory/base/categories/karoubi-filtration-sums.md)). Concretely, the sum of the $r$-split of $M$ and the $s$-split of $N$ lies below the $\max(r,s)$-split of $M\oplus N$, although it is in general not itself a chosen split. Closure under isomorphism is neither claimed nor needed.

## Sources

- HS paper, Section 2
- [Carlsson-Pedersen 1995, Def 1.27](../../../../sources/paper/carlsson-pedersen-1995.md) [U]

## Depends on

- [Support subcategory](support-subcategory.md)
- [Involution-invariant Karoubi filtration](../../l-theory/base/categories/karoubi-filtration.md)

## Proof depends on

- [Support ideal](support-ideal.md)
