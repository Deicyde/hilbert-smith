---
article_id: af_ccb69209a07cf8fd4c9ddaf9
declaration: def
origin: bridged
statement: formalized
lean: HSP.iteratedQuotient
---

# Iterated quotient

Let $S,Y,Z\subset X$. The identity on objects and on representatives gives mutually inverse strict duality functors $(\mathcal A_S/\mathcal A_Z)/\mathcal U_Y\cong\mathcal A_S/\mathcal A_{Y\cup Z}$, which commute with the quotient functors from $\mathcal A_S$. The outer quotient is by the [supported objects of the support quotient](quotient-support.md) $\mathcal U_Y$, the subcategory of the [quotient support filtration](quotient-support-filtration.md). Neither closedness nor invariance is used.

*Proof sketch.* A map $[f]$ factors through a $Y$-supported object in $\mathcal A_S/\mathcal A_Z$ iff $f\in I_Y+I_Z$, so the left hom-sets are $\mathrm{Hom}/(I_Y+I_Z)$. $I_Y+I_Z\subset I_{Y\cup Z}$, because $Y$- and $Z$-supported objects are $(Y\cup Z)$-supported and the ideal is closed under sums. Conversely, let $f=hg$ through $W\in\mathcal A_{Y\cup Z}$ whose labels lie in $\overline N_{a_i}(Y\cup Z)$ with $a$ null. Split $W$ into the labels in $\overline N_{a_i}(Y)$, which form a $Y$-supported part, and the rest, which lie in $\overline N_{a_i}(Z)$. Then $f=h\iota_Y\pi_Yg+h\iota_Z\pi_Zg$. Disjointness is not used.

## Sources

- HS paper, Section 6
- New: two-stage quotient identified with one quotient by the union.

## Depends on

- [Quotient support filtration](quotient-support-filtration.md)
- [Support filtration](support-filtration.md)
- [Supported objects of a support quotient](quotient-support.md)
- [Supported objects of a support quotient are additive](quotient-support-additive.md)
- [Support subcategory inside a support subcategory](relative-support.md)
- [The support subcategory inside a support subcategory is additive](relative-support-additive.md)
- [Duality functor](../../l-theory/base/categories/duality-functor.md)
- [The quotient duality functor](../../l-theory/base/categories/quotient-duality-functor.md)

## Proof depends on

- [Lift of a duality functor to a quotient](../../l-theory/base/categories/quotient-dual-lift.md)
- [Null thickening radii](null-thickening.md)
- [Inclusion after projection](../asymptotic/restriction/projection-inclusion.md)
- [Complementary diagonal projection](../asymptotic/restriction/diagonal-projection-complement.md)
- [Enumerated indices satisfy the predicate](../asymptotic/restriction/restriction-index-mem.md)
- [Maps factoring through a dual-closed subcategory form an ideal](../../l-theory/base/categories/filtration-ideal-closure.md)
- [Maps factoring through a subcategory](../../l-theory/base/categories/filtration-ideal.md)
- [Restriction to a sub-basis](../asymptotic/restriction/restriction-sub-basis.md)
- [Enumeration of a sub-basis](../asymptotic/restriction/restriction-index-embedding.md)
- [Coordinate inclusion of a restriction](../asymptotic/restriction/coordinate-inclusion.md)
- [Coordinate projection onto a restriction](../asymptotic/restriction/coordinate-projection.md)
- [Asymptotic category](../asymptotic/asymptotic-category.md)
- [Quotient by a subcategory](../../l-theory/base/categories/filtration-quotient.md)
- [Additive subcategory closed under duality](../../l-theory/base/categories/dual-additive-subcategory.md)
