---
article_id: af_9cd579f4efc6f778f98513cb
declaration: def
origin: bridged
statement: formalized
proof: formalized
lean: HSP.AsymPre.trunc
---

# Diagonal coordinate projection

Let $P$ be a decidable predicate on the indices of an object $M$ of the [asymptotic category](../asymptotic-category.md). The diagonal coordinate projection $p_P:M\to M$ is, at level $i$, the diagonal matrix with entry $1$ at $(g,k)$ if $P(i,k)$ and $0$ otherwise. It is $G_i$-equivariant and has [propagation](../propagation.md) $0$.

*Proof sketch.* A diagonal matrix whose entries depend only on $k$ is equivariant, and its nonzero entries join a basis element to itself.

## Sources

- HS paper, Section 2
- New: a named step of the support calculus.

## Depends on

- [Asymptotic category](../asymptotic-category.md)
- [Propagation](../propagation.md)
- [Free category of a finite group](../free-category.md)
