---
article_id: af_d1741c61cb3af86d5639a11d
declaration: def
origin: bridged
statement: formalized
lean: HSP.SCat.karoubiFiltration
---

# Point filtration

$\mathcal S_{\mathbf G}\subset\mathcal P_{\mathbf G}$ is an [involution-invariant Karoubi filtration](../../l-theory/base/categories/karoubi-filtration.md). The chosen decompositions of $M=(n_i)$ are the truncations $p_N$, $N\in\mathbb N$: $p_N$ is the identity in the coordinates $i<N$ and zero in the coordinates $i\ge N$. It splits through $M_{<N}$, which has $n_i$ in the coordinates $i<N$ and the zero object elsewhere, and $1-p_N$ splits through $M_{\ge N}$, which has $n_i$ in the coordinates $i\ge N$ and the zero object elsewhere. The inclusions and projections are identity matrices in the coordinates where they are defined.

*Proof sketch.*
1. $\mathcal S_{\mathbf G}$ is a full additive subcategory with $\mathcal S_{\mathbf G}^*\subset\mathcal S_{\mathbf G}$: a sum of finitely supported sequences is finitely supported, and $M^*=M$.
2. $M_{<N}$ lies in $\mathcal S_{\mathbf G}$, and the splitting identities hold coordinatewise.
3. $N\le N'$ gives $p_N\le p_{N'}$, so the family is directed.
4. (Factorization.) If $V=(m_i)$ is the zero object in every coordinate $i\ge N$, then every $g:V\to M$ has $p_Ng=g$ and every $h:M\to V$ has $hp_N=h$.
5. (Duality.) $p_N^{T}=p_N$ and $M^*=M$.

## Sources

- HS paper, Section 3
- [Carlsson-Pedersen 1995, Def 1.27](../../../../sources/paper/carlsson-pedersen-1995.md) [U]

## Depends on

- [Finite-support subcategory](eventually-zero-subcategory.md)
- [Involution-invariant Karoubi filtration](../../l-theory/base/categories/karoubi-filtration.md)
