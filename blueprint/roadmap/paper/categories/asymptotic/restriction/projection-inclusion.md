---
article_id: af_4b1bab98602a81f58f7b7dda
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.AsymPre.restrictPro_restrictInc
---

# Inclusion after projection

For a [restriction](restriction-sub-basis.md) $M_P$ and decidable $P$, the [coordinate inclusion](coordinate-inclusion.md) after the [coordinate projection](coordinate-projection.md) is the [diagonal coordinate projection](diagonal-projection.md) onto the indices with $P$: $\iota\pi=p_P$.

*Proof sketch.* $\iota\iota^T$ is the diagonal matrix with $1$ exactly at the basis elements whose index is enumerated, and these are the indices with $P$ ([enumerated indices satisfy the predicate](restriction-index-mem.md)).

## Sources

- HS paper, Section 2
- New: a named step of the support calculus.

## Depends on

- [Coordinate inclusion of a restriction](coordinate-inclusion.md)
- [Coordinate projection onto a restriction](coordinate-projection.md)
- [Diagonal coordinate projection](diagonal-projection.md)

## Proof depends on

- [Enumerated indices satisfy the predicate](restriction-index-mem.md)
- [The inclusion matrix](../structure/inclusion-matrix.md)
