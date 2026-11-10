---
article_id: af_0bca0b3fa2316d3c2bac1813
declaration: def
origin: bridged
---

# Support filtrations in a quotient

Let $Y,Z\subset S\subset X$ be closed and invariant, and let $\mathcal U_Y$ be the predicate "$Y$-supported" on the objects of $\mathcal A_S/\mathcal A_Z$. Then $\mathcal U_Y$ is an involution-invariant Karoubi filtration of $\mathcal A_S/\mathcal A_Z$. Its chosen decompositions are the images of the splits of the [support filtration](support-filtration.md) for $Y\subset S$. No disjointness of $Y$ and $Z$ is assumed.

*Proof sketch.* The quotient functor $q$ is the identity on objects, additive and strictly duality-preserving. So it carries the chosen splits to splits with the same order, and self-transpose projections to self-transpose projections. The images are directed. A map $[g]:V\to M$ with $V$ $Y$-supported has a representative $g$ in $\mathcal A_S$, and $g=\iota\pi g$ for some split, so $[g]=[\iota][\pi][g]$. Maps into $V$ are handled by transposing. $\mathcal U_Y$ is not closed under isomorphism ($M_Y\oplus M_Z\cong M_Y$), and the definition does not require it.

## Sources

- HS paper, Section 6

## Depends on

- [Support filtration](support-filtration.md)
- [Quotient by a filtration](../../l-theory/base/categories/filtration-quotient.md)
- [Involution-invariant Karoubi filtration](../../l-theory/base/categories/karoubi-filtration.md)
