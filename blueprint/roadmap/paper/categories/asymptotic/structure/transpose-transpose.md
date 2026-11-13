---
article_id: af_6d3a39352271b01e5c5d8ef0
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.AsymPre.transpose_transpose
---

# Transposing twice

For a sequence $u$ of matrices of the [asymptotic category](../asymptotic-category.md), the [levelwise transpose](levelwise-transpose.md) of the levelwise transpose of $u$ is $u$.

*Proof sketch.* $(u_i^T)^T=u_i$ at every level.

## Sources

- HS paper, Section 2

## Depends on

- [The levelwise transpose](levelwise-transpose.md)
- [Asymptotic category](../asymptotic-category.md)
- [Group sequence](../group-sequence.md)

## Proof depends on

- [Free category of a finite group](../free-category.md)
