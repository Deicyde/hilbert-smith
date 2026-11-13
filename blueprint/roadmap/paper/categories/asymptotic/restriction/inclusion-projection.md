---
article_id: af_05c796d148cc56e95beea372
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.AsymPre.restrictInc_restrictPro
---

# Projection after inclusion

For a [restriction](restriction-sub-basis.md) $M_P$, the [coordinate projection](coordinate-projection.md) after the [coordinate inclusion](coordinate-inclusion.md) is the identity: $\pi\iota=1$.

*Proof sketch.* $\iota^T\iota=1$ because the enumeration of the indices with $P$ is injective.

## Sources

- HS paper, Section 2
- New: a named step of the support calculus.

## Depends on

- [Coordinate inclusion of a restriction](coordinate-inclusion.md)
- [Coordinate projection onto a restriction](coordinate-projection.md)
- [Asymptotic category](../asymptotic-category.md)
- [Group sequence](../group-sequence.md)
- [Restriction to a sub-basis](restriction-sub-basis.md)

## Proof depends on

- [The inclusion matrix](../structure/inclusion-matrix.md)
- [Free category of a finite group](../free-category.md)
- [Enumeration of a sub-basis](restriction-index-embedding.md)
