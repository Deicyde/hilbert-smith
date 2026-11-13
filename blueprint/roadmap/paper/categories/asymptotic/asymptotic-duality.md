---
article_id: af_545fb65fc416fbfc3bb9fe70
declaration: instance
origin: bridged
statement: formalized
lean: HSP.AsymCat.dualCat
---

# Duality on the asymptotic category

$\mathcal A_{\mathbf G}(X)$ is a [strict duality category](../../l-theory/base/categories/duality-category.md) under $M^*=M$ and $[u_i]^*=[u_i^{T}]$.

*Proof sketch.* On representing sequences the dual is the [levelwise transpose](structure/levelwise-transpose.md), which keeps propagation. It respects eventual equality, so it descends to classes; it reverses composition, is $\mathbb Q$-linear and is an involution on the nose.

## Sources

- HS paper, Section 2

## Depends on

- [Asymptotic category](asymptotic-category.md)
- [Strict duality category](../../l-theory/base/categories/duality-category.md)
- [The asymptotic category has finite biproducts](structure/biproducts.md)
- [Group sequence](group-sequence.md)

## Proof depends on

- [Equality of classes](structure/class-eq.md)
- [Every morphism is a class](structure/class-surjective.md)
- [Free category of a finite group](free-category.md)
- [Transposing twice](structure/transpose-transpose.md)
- [The levelwise transpose](structure/levelwise-transpose.md)
