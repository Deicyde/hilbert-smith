---
article_id: af_7b4ea61e7b3604dc26435a7a
declaration: instance
origin: bridged
statement: formalized
lean: HSP.isDualAdditive_exInter
---

# Supported objects of a relative support subcategory are additive

For $S,A,B\subset X$, let $\mathcal U_A$ be the full subcategory of $A$-supported objects of $\mathcal A_S$ ([support subcategory inside a support subcategory](relative-support.md)). Its $B$-supported objects, the intersection $\mathcal U_A\cap\mathcal U_B$ of an [excisive pair](../../l-theory/ultimate/boundary/excisive-pair.md), form a full additive subcategory of $\mathcal U_A$ closed under duality.

*Proof sketch.* The empty sequence and the [concatenation](support-concatenation.md) of two objects lie in all three support subcategories, they are a zero object and a biproduct in $\mathcal U_A$, and $M^*=M$.

## Sources

- HS paper, Section 2
- New: a named step of the support calculus.

## Depends on

- [Intersection of full subcategories](../../l-theory/ultimate/boundary/excisive-intersection.md)
- [Support subcategory inside a support subcategory](relative-support.md)
- [The support subcategory inside a support subcategory is additive](relative-support-additive.md)
- [Excisive pair of filtrations](../../l-theory/ultimate/boundary/excisive-pair.md)

## Proof depends on

- [Concatenation of supported objects](support-concatenation.md)
