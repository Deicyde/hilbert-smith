---
article_id: af_628d6508f3fe2fa851bd2881
declaration: instance
origin: bridged
statement: formalized
lean: HSP.isDualAdditive_suppIn
---

# The support subcategory inside a support subcategory is additive

For all $S,S'\subset X$, $\mathcal A_{S'}\subset\mathcal A_S$ ([support subcategory inside a support subcategory](relative-support.md)) is a full additive subcategory closed under duality. So the quotient $\mathcal A_S/\mathcal A_{S'}$ exists.

*Proof sketch.* The witnesses are the empty sequence, a zero object of $\mathcal A_S$; the concatenation of two objects, a biproduct in $\mathcal A_S$; and $M^*=M$. The empty sequence is supported on every set, and [concatenations](support-concatenation.md) of supported objects are supported.

## Sources

- HS paper, Section 2
- New: a named step of the support calculus.

## Depends on

- [Support subcategory inside a support subcategory](relative-support.md)
- [Additive subcategory closed under duality](../../l-theory/base/categories/dual-additive-subcategory.md)

## Proof depends on

- [Concatenation of supported objects](support-concatenation.md)
