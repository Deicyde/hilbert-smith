---
article_id: af_411277b8d9d19ca34a93f52c
declaration: def
origin: bridged
statement: formalized
lean: HSP.quotientSeparationIso
---

# Separated support in a quotient

Let $X$ be compact with an isometric $C_p$-action, let $S\subset X$, and let $Y,Z\subset X$ be closed and invariant with $Y\subset S$ and $Y\cap Z=\varnothing$. Let $\mathcal U_Y\subset\mathcal A_S/\mathcal A_Z$ be the [$Y$-supported objects](quotient-support.md) of the quotient of $\mathcal A_S$ by the [support subcategory](relative-support.md) $\mathcal A_Z\subset\mathcal A_S$. The quotient functor $\mathcal A_Y\to\mathcal U_Y$, $M\mapsto M$, $u\mapsto[u]$, and its inverse $\sigma:\mathcal U_Y\to\mathcal A_Y$, which is the identity on objects, are mutually inverse strict [duality functors](../../l-theory/base/categories/duality-functor.md).

*Proof sketch.* The functor is a bijection on objects by the definition of $\mathcal U_Y$, and surjective on morphisms because it is a quotient. It is injective on morphisms: if $[u]=[u']$ in $\mathcal A_S/\mathcal A_Z$, then $u-u'$ factors through an object of $\mathcal A_Z$ and its target is $Y$-supported, so it [vanishes](disjoint-support-vanishing.md) (the argument of separation). The inverse is the inverse bijection on hom-sets. Strictness holds because $q$ commutes with transpose.

**Remark (not formalized).** In the uses also $Z\subset S$ and $S$ is closed and invariant; the statement does not need this.

## Sources

- HS paper, Section 6

## Depends on

- [Quotient by a filtration](../../l-theory/base/categories/filtration-quotient.md)
- [Support subcategory](support-subcategory.md)
- [The support subcategory is additive](support-dual-additive.md)
- [Support subcategory inside a support subcategory](relative-support.md)
- [Supported objects of a support quotient](quotient-support.md)
- [Supported objects of a support quotient are additive](quotient-support-additive.md)
- [Duality functor](../../l-theory/base/categories/duality-functor.md)

## Proof depends on

- [Maps through a disjoint support vanish](disjoint-support-vanishing.md)
- [Maps factoring through a subcategory](../../l-theory/base/categories/filtration-ideal.md)
- [Additive subcategory closed under duality](../../l-theory/base/categories/dual-additive-subcategory.md)
- [Every morphism is a class](../asymptotic/structure/class-surjective.md)
