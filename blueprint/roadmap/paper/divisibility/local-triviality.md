---
article_id: af_cd693c188b7f6f80e2069c55
declaration: lemma
origin: bridged
---

# Local triviality

Let $S\subseteq X$ be closed and invariant. Suppose there is a continuous map $c:S\to C_p$ with $c(gx)=g+c(x)$. Then $\nu_S=0$ on $\mathbb L_k(\mathcal A_S)$ for all $k$.

*Proof sketch.*
1. The sheets $c^{-1}(j)$ are compact and pairwise disjoint, so they are separated by some $\delta>0$. A point within $\delta/3$ of $S$ is within $\delta/3$ of exactly one sheet; call its index $\bar c$. Isometry gives $\bar c(gx)=g+\bar c(x)$.
2. For an object of $\mathcal A_S$, all labels are eventually within $\delta/3$ of $S$.
3. Send the basis element $(q,b)$ to $b$ in copy $\chi_i(q)-\bar c(\ell_i(b))$. This is an equivariant, label-preserving bijection of bases, so it gives an orthogonal isomorphism $\tau\otimes M\cong M^{\oplus p}$ of propagation $0$.
4. Once the propagation is below $\delta/3$, a nonzero entry joins labels near the same sheet. Hence the isomorphism is natural, modulo eventual equality.
5. The isomorphism is unitary, so by D2 $(\tau\otimes)_*=p\cdot\mathrm{id}$.

## Sources

- HS paper, Section 4 (Local triviality).
- New: sheet index taken near $S$ itself, with no trivializing neighborhood.

## Depends on

- [The endomorphism $\nu$](permutation-nu.md)

## Proof depends on

- [Functoriality on ultimate L](../l-theory/ultimate/groups/induced-map-comp.md)
