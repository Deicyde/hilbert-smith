---
article_id: af_27ccd0b4797a657ae51bbe22
declaration: lemma
origin: bridged
---

# Interiors of fixed sets are closed

Let $p$ be a prime and let $\mathbb Z_p$ act jointly continuously on an $n$-manifold $M$. Suppose every point of $M$ has a neighbourhood fixed pointwise by some $H_\ell$. Then for every $j$ the interior $F_j$ of $\operatorname{Fix}_j(M)$ is closed.

*Proof sketch.* Take $x\in\overline{F_j}$.
1. $\operatorname{Fix}_j(M)$ is closed, so $H_j$ fixes $x$.
2. By hypothesis $x$ lies in the open set $N=\operatorname{int}\operatorname{Fix}_\ell(M)$ for some $\ell$.
3. $H_jx=\{x\}\subseteq N$, so compactness of $H_j$ and the tube lemma give a connected coordinate ball $B\ni x$ with $H_jB\subseteq N$.
4. The saturation $N'=H_jB$ is open, $H_j$-invariant, and connected, since every translate of $B$ contains $x$. As an open subset of $M$ it is a connected $n$-manifold.
5. Each $a\in H_j$ restricts to a homeomorphism of $N'$ whose $p^\ell$-th power is the identity, because $p^\ell a\in H_\ell$ fixes $N\supseteq N'$. It fixes pointwise the open set $N'\cap F_j$, which is nonempty because $x\in\overline{F_j}$.
6. Newman's theorem on fixing an open set makes $a$ the identity on $N'$. So $N'\subseteq\operatorname{Fix}_j(M)$, and $x\in F_j$.

## Sources

- [OpenAI preprint, Section 5](../../../../sources/preprint.md#section-5-local-tests-sections05-local-teststex), 05-local-tests.tex lines 36-50

## Depends on

- [Fixed sets of the subgroups $H_j$](fixed-sets.md)

## Proof depends on

- [Fixed sets are closed](fixed-sets-closed.md)
- [The subgroups $H_j$ form a basis at $0$](padic-subgroups-basis.md)
- [Newman's theorem: fixing an open set](../../inputs/newman/newman-open-set.md)
