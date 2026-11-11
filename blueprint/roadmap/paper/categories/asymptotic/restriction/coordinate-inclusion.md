---
article_id: af_eec4058ca891f1d05696e509
declaration: def
origin: bridged
statement: formalized
proof: formalized
lean: HSP.AsymPre.restrictInc
---

# Coordinate inclusion of a restriction

For a [restriction](restriction-sub-basis.md) $M_P$ of $M$, the coordinate inclusion $\iota:M_P\to M$ is, at level $i$, the matrix with entry $1$ at $((g,e_i(k)),(g,k))$ and $0$ elsewhere, where $e_i$ is the [enumeration](restriction-index-embedding.md) of the indices with $P$. It is a morphism of the asymptotic category (its matrices are $G_i$-equivariant with [propagation](../propagation.md) $0$).

*Proof sketch.* Both endpoints of a nonzero entry carry the label $\chi_i(g)+x_i(e_i(k))$.

## Sources

- HS paper, Section 2
- New: a named step of the support calculus.

## Depends on

- [Restriction to a sub-basis](restriction-sub-basis.md)
- [Enumeration of a sub-basis](restriction-index-embedding.md)
- [Propagation](../propagation.md)
- [Free category of a finite group](../free-category.md)
- [The inclusion matrix](../structure/inclusion-matrix.md)
