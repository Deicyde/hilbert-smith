---
article_id: af_0bca0b3fa2316d3c2bac1813
declaration: def
origin: bridged
statement: formalized
lean: HSP.quotSupp_karoubiFiltration
---

# Support filtrations in a quotient

Let $S,Y,Z\subset X$, and let $\mathcal U_Y\subset\mathcal A_S/\mathcal A_Z$ be the [supported objects of the support quotient](quotient-support.md), a full additive subcategory closed under duality ([additivity](quotient-support-additive.md)). If the action is isometric and $Y$ is invariant, $\mathcal U_Y$ is an involution-invariant Karoubi filtration of $\mathcal A_S/\mathcal A_Z$. Its chosen decompositions are the images of the splits of the [support filtration](support-filtration.md) for $Y\subset S$. No disjointness of $Y$ and $Z$ is assumed, and neither closedness nor $Y,Z\subset S$ is used.

*Proof sketch.* The quotient functor $q$ is the identity on objects, additive and strictly duality-preserving. So it carries the chosen splits to splits with the same order, and self-transpose projections to self-transpose projections. The images are directed. A map $[g]:V\to M$ with $V$ $Y$-supported has a representative $g$ in $\mathcal A_S$, and $g=\iota\pi g$ for some split, so $[g]=[\iota][\pi][g]$. Maps into $V$ are handled by transposing. $\mathcal U_Y$ is not closed under isomorphism ($M_Y\oplus M_Z\cong M_Y$), and the definition does not require it.

## Sources

- HS paper, Section 6

## Depends on

- [Supported objects of a support quotient](quotient-support.md)
- [Supported objects of a support quotient are additive](quotient-support-additive.md)
- [Support filtration](support-filtration.md)
- [Quotient by a filtration](../../l-theory/base/categories/filtration-quotient.md)
- [Involution-invariant Karoubi filtration](../../l-theory/base/categories/karoubi-filtration.md)

## Proof depends on

- [Transposing twice](../asymptotic/structure/transpose-transpose.md)
