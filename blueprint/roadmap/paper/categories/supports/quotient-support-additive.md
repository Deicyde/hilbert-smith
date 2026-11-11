---
article_id: af_58f9e6cdd072dec48bc654a8
declaration: instance
origin: bridged
statement: formalized
lean: HSP.isDualAdditive_quotSupp
---

# Supported objects of a support quotient are additive

For all $S,Z,Y\subset X$, $\mathcal U_Y\subset\mathcal A_S/\mathcal A_Z$ ([supported objects of a support quotient](quotient-support.md)) is a full additive subcategory closed under duality.

*Proof sketch.* The additive, strictly duality-preserving quotient functor carries a zero object and biproducts of $\mathcal A_Y\subset\mathcal A_S$ ([additive](relative-support-additive.md)) to a zero object and biproducts, and $M^*=M$.

## Sources

- HS paper, Section 2
- New: a named step of the support calculus.

## Depends on

- [Supported objects of a support quotient](quotient-support.md)
- [Additive subcategory closed under duality](../../l-theory/base/categories/dual-additive-subcategory.md)

## Proof depends on

- [The support subcategory inside a support subcategory is additive](relative-support-additive.md)
