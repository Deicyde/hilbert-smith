---
article_id: af_52f30915f27289e383a977fe
declaration: def
origin: bridged
---

# The finite-support filtration

On an object $M=(B_i)$ of $\mathcal P$, the chosen $\mathcal S$-projections are the diagonal idempotents $1_A$ for coordinatewise $G_i$-invariant subsets $A=(A_i)$, $A_i\subset B_i$, with $A_i=\varnothing$ for almost all $i$. This makes $\mathcal S$ an involution-invariant Karoubi filtration of $\mathcal P$.

*Proof sketch.* $1_A$ factors through the object $(A_i)$ of $\mathcal S$, and $1-1_A=1_{B\setminus A}$ splits. The family is directed under union. (1) A map to or from an object supported on a finite set $F$ is fixed by $1_A$ with $A_i=B_i$ for $i\in F$ and $A_i=\varnothing$ otherwise. (2) On $M\oplus N$, $1_A\oplus1_{A'}=1_{A\sqcup A'}$. (3) $1_A^T=1_A$ and $M^*=M$. $\mathcal S$ is closed under isomorphism because an invertible equivariant matrix is square, and $\mathcal S^*=\mathcal S$.

## Sources

- HS paper, Section 3
- [Carlsson-Pedersen 1995, Def 1.27](../../../../sources/paper/carlsson-pedersen-1995.md) [U]

## Depends on

- [The sequence category](sequence-categories.md)
- [Involution-invariant Karoubi filtration](../../l-theory/base/categories/karoubi-filtration.md)
