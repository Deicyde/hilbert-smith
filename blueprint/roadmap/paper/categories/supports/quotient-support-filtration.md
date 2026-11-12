---
article_id: af_0bca0b3fa2316d3c2bac1813
declaration: def
origin: bridged
statement: formalized
lean: HSP.quotSupp_karoubiFiltration
---

# Support filtrations in a quotient

Let $S,Y,Z\subset X$, and let $\mathcal U_Y\subset\mathcal A_S/\mathcal A_Z$ be the [supported objects of the support quotient](quotient-support.md), a full additive subcategory closed under duality ([additivity](quotient-support-additive.md)). If the action is isometric and $Y$ is invariant, $\mathcal U_Y$ is an involution-invariant Karoubi filtration of $\mathcal A_S/\mathcal A_Z$. Its chosen decompositions are the images of the splits of the [support filtration](support-filtration.md) for $Y\subset S$. No disjointness of $Y$ and $Z$ is assumed, and neither closedness nor $Y,Z\subset S$ is used.

*Proof sketch.* The quotient functor $q$ is the identity on objects, additive and strictly duality-preserving. So it carries the chosen splits to splits with the same order, and self-transpose projections to self-transpose projections; for the converse, transposing twice is the identity on classes ([every morphism is a class](../asymptotic/structure/class-surjective.md), [transposing twice](../asymptotic/structure/transpose-transpose.md)). The images are directed. A map $V\to M$ with $V$ $Y$-supported is the class $[g]$ of a map $g$ of $\mathcal A_S$, since the quotient functor of the [quotient by a subcategory](../../l-theory/base/categories/filtration-quotient.md) is surjective on maps. By the [support filtration](support-filtration.md), $g=\iota\pi g$ for some chosen split, so $[g]=[\iota][\pi][g]$. A map $M\to V$ is handled directly in the same way, with the support filtration's factorization $g=g\iota\pi$ on the other side. $\mathcal U_Y$ is not closed under isomorphism ($M_Y\oplus M_Z\cong M_Y$), and the definition does not require it.

## Sources

- HS paper, Section 6

## Depends on

- [Supported objects of a support quotient](quotient-support.md)
- [Supported objects of a support quotient are additive](quotient-support-additive.md)
- [Quotient by a filtration](../../l-theory/base/categories/filtration-quotient.md)
- [Involution-invariant Karoubi filtration](../../l-theory/base/categories/karoubi-filtration.md)
- [Group sequence](../asymptotic/group-sequence.md)

## Proof depends on

- [Support filtration](support-filtration.md)
- [Support subcategory inside a support subcategory](relative-support.md)
- [Every morphism is a class](../asymptotic/structure/class-surjective.md)
- [Duality on the asymptotic category](../asymptotic/asymptotic-duality.md)
- [Small Q-linear category with strict duality](../../l-theory/base/categories/duality-category.md)
- [Transposing twice](../asymptotic/structure/transpose-transpose.md)
