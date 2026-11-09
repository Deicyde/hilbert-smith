---
article_id: af_251cccb60e3303ff0ab37e1a
declaration: theorem
origin: bridged
---

# Local exclusion

Let $p$ be a prime, $n\in\mathbb N$, and $O\subseteq\mathbb{R}^n$ a nonempty connected open set. No jointly continuous action of $\mathbb{Z}_p$ on $O$ is faithful.

*Proof sketch.*
1. If $n=0$, $O$ is a point, and $0$ and $1$ act alike.
2. Otherwise suppose the action is faithful. $O$ is a connected $n$-manifold, so it carries fixed local data with $D=1/64$.
3. From fixed local data, Theorem C of a later chapter builds a controlled Poincaré complex over $T\times S^n$, with $T$ the control space, and its tail of signatures $(s_k)$.
4. Theorem B (evaluation) gives $s_k\in\{1,-1\}$ for all large $k$.
5. Theorem A (divisibility) gives $p\mid s_k$ for all large $k$.
6. The lemma on integer tails gives a contradiction.

## Sources

- [HS paper, Section 13](../../../sources/hs-paper.md#section-13-the-contradiction-seccontradiction-lines-1326-1391) (Proposition 13.1 and the proof of Theorem 1.1)
- [HS paper, Section 4](../../../sources/hs-paper.md#section-4-divisibility-over-a-free-c_p-space-algobstruction-lines-317-380)

## Depends on

## Proof depends on

- [Fixed local data from a faithful action](../local-data/control/fixed-local-data-exists.md)
- [Integer tails](integer-tails.md)
