---
article_id: af_d7a19fdf17957ab9929d0f0e
declaration: instance
origin: bridged
statement: formalized
lean: HSP.isDualAdditive_supp
---

# The support subcategory is additive

For every $S\subset X$, the [support subcategory](support-subcategory.md) $\mathcal A_S$ is a [full additive subcategory closed under duality](../../l-theory/base/categories/dual-additive-subcategory.md) of the [asymptotic category](../asymptotic/asymptotic-category.md) with its [duality](../asymptotic/asymptotic-duality.md). So the quotient by $\mathcal A_S$ exists.

*Proof sketch.* The witnesses are the empty object, a zero object; the concatenation of two objects with the coordinate inclusions and projections, a biproduct; and $M^*=M$. The empty object has no labels, so it is supported on every set. Eventually the labels of both pieces of a concatenation lie in the $\varepsilon$-thickening of $S$. $M^*$ has the same labels as $M$.

## Sources

- HS paper, Section 2
- New: a named step of the support calculus.

## Depends on

- [Support subcategory](support-subcategory.md)
- [Additive subcategory closed under duality](../../l-theory/base/categories/dual-additive-subcategory.md)
- [Asymptotic category](../asymptotic/asymptotic-category.md)
- [Duality on the asymptotic category](../asymptotic/asymptotic-duality.md)
- [Group sequence](../asymptotic/group-sequence.md)
- [The asymptotic category has finite biproducts](../asymptotic/structure/biproducts.md)

## Proof depends on

- [The concatenation is a biproduct](../asymptotic/structure/concatenation-bilimit.md)
- [Concatenation](../asymptotic/structure/concatenation.md)
- [The empty sequence is a zero object](../asymptotic/structure/empty-object-zero.md)
- [The empty sequence](../asymptotic/structure/empty-object.md)
