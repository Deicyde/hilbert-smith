---
article_id: af_87b8381fb104ae61710475be
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.separation
---

# Separation

Let $X$ be compact with an isometric $C_p$-action. If $S,Z\subset X$ are disjoint closed invariant sets, the quotient functor restricted to $\mathcal A_S\to\mathcal A_{\mathbf G}(X)/\mathcal A_Z$ is fully faithful.

*Proof sketch.* Fullness holds because the functor is a quotient. For faithfulness, let $f,g$ be maps between $S$-supported objects with the same image. Two maps have the same class in the [quotient by a subcategory](../../l-theory/base/categories/filtration-quotient.md) exactly when their difference factors through an object of $\mathcal A_Z$. [Every morphism is a class](../asymptotic/structure/class-surjective.md), $f-g=[u]$, and $[u]$ has an $S$-supported target, so it is zero because [maps through a disjoint support vanish](disjoint-support-vanishing.md). So $f=g$.

## Sources

- HS paper, Section 2

## Depends on

- [Group sequence](../asymptotic/group-sequence.md)
- [Asymptotic category](../asymptotic/asymptotic-category.md)
- [Support subcategory](support-subcategory.md)
- [Quotient by a subcategory](../../l-theory/base/categories/filtration-quotient.md)

## Proof depends on

- [Maps through a disjoint support vanish](disjoint-support-vanishing.md)
- [Every morphism is a class](../asymptotic/structure/class-surjective.md)
- [Duality on the asymptotic category](../asymptotic/asymptotic-duality.md)
- [The asymptotic category has finite biproducts](../asymptotic/structure/biproducts.md)
- [The support subcategory is additive](support-dual-additive.md)
- [Maps factoring through a subcategory](../../l-theory/base/categories/filtration-ideal.md)
