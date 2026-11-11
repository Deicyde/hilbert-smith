---
article_id: af_cf08b32d13cde4386009f4e6
declaration: def
origin: bridged
statement: formalized
lean: HSP.AsymPre.restrict
---

# Restriction to a sub-basis

Let $M=(n_i,x_i)$ be an object of the [asymptotic category](asymptotic-category.md) and $P$ a predicate on its indices $(i,k)$. The restriction $M_P$ keeps the indices $k$ with $P(i,k)$, in increasing order, with their labels. The coordinate inclusion $\iota:M_P\to M$ and the projection $\pi=\iota^T:M\to M_P$ have [propagation](propagation.md) $0$, with $\pi\iota=1$ and $\iota\pi=p_P$, the diagonal coordinate projection of $M$ onto the indices with $P$. Moreover $p_{\neg P}=1-p_P$, $p_Q\,p_P=p_{P\wedge Q}$ and $p_P^T=p_P$.

*Proof sketch.* The inclusion matrix has its nonzero entries, all equal to $1$, at $((g,e(k)),(g,k))$, where $e$ enumerates the indices with $P$; both endpoints carry the same label, so the propagation is $0$, and it is $G_i$-equivariant. Since $e$ is injective, $\iota^T\iota=1$, and $\iota\iota^T$ is the diagonal matrix with $1$ exactly at the basis elements $(g,j)$ with $j$ in the range of $e$, which are those with $P(i,j)$. The identities for $p_P$ are identities of diagonal matrices.

## Sources

- HS paper, Section 2
- New: the sub-basis restriction used in the support ideal and the support filtration.

## Depends on

- [Asymptotic category](asymptotic-category.md)
- [Duality on the asymptotic category](asymptotic-duality.md)
- [Propagation](propagation.md)
