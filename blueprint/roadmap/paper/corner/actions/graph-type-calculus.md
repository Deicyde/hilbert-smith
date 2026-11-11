---
article_id: af_c6a5714f090414b80d062bb5
declaration: lemma
origin: bridged
---

# Calculus of graph types

Let $X$ be as in [Graph-type matrices](graph-type.md), and let $c,c'\in C_p$.
1. If $u:M\to M'$ has graph type $c$ with bound $e$ and $u':M'\to M''$ has graph type $c'$ with bound $e'$, then $u'u$ has graph type $c+c'$ with bound $e+e'$.
2. If $u:M\to M'$ has graph type $c$ with bound $e$, then its transpose $u^*:M'\to M$ has graph type $-c$ with bound $e$.
3. If $K$ is a finite nonempty set and each $u_k:M\to M'$ ($k\in K$) has graph type $c$ with bound $e_k$, then $\sum_ku_k$ has graph type $c$ with bound $\max_ke_k$.

*Proof sketch.*
1. A nonzero entry $(u'u)_{b''b}=\sum_{b'}u'_{b''b'}u_{b'b}$ has some $b'$ with both factors nonzero. Then $d(\lambda_{b''},(c+c')\cdot\lambda_b)\le d(\lambda_{b''},c'\cdot\lambda_{b'})+d(c'\cdot\lambda_{b'},c'\cdot(c\cdot\lambda_b))\le e'+e$, because $c'$ acts isometrically.
2. $(u^*)_{bb'}=u_{b'b}$, and $d(\lambda_b,(-c)\cdot\lambda_{b'})=d(c\cdot\lambda_b,\lambda_{b'})\le e$ by isometry.
3. A nonzero entry of the sum is a nonzero entry of some $u_k$.

## Sources

- HS paper, Section 9 (used there without a separate statement).
- New: stated once for any isometric $C_p$-space.

## Depends on

- [Graph-type matrices](graph-type.md)
