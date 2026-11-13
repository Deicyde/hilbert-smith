---
article_id: af_cf08b32d13cde4386009f4e6
declaration: def
origin: bridged
statement: formalized
lean: HSP.AsymPre.restrict
---

# Restriction to a sub-basis

Let $M=(n_i,x_i)$ be an object of the [asymptotic category](../asymptotic-category.md) and $P$ a predicate on its indices $(i,k)$. The restriction $M_P=(m_i,\,x_i\circ e_i)$ keeps the indices $k$ with $P(i,k)$, in increasing order, with their labels; here $e_i$ is the [enumeration](restriction-index-embedding.md) of these indices and $m_i$ their number.

## Sources

- HS paper, Section 2
- New: the sub-basis restriction used in the support ideal and the support filtration.

## Depends on

- [Asymptotic category](../asymptotic-category.md)
- [Group sequence](../group-sequence.md)

## Proof depends on

- [Enumeration of a sub-basis](restriction-index-embedding.md)
