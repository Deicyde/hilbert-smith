---
article_id: af_411277b8d9d19ca34a93f52c
declaration: def
origin: bridged
---

# Separated support in a quotient

Let $Y,Z\subset S\subset X$ be closed and invariant with $Y\cap Z=\varnothing$. The quotient functor $\mathcal A_Y\to\mathcal U_Y\subset\mathcal A_S/\mathcal A_Z$ and its inverse, which is the identity on objects, are mutually inverse strict duality functors.

*Proof sketch.* The functor is a bijection on objects by the definition of $\mathcal U_Y$. Hom-sets of $\mathcal A_S/\mathcal A_Z$ between $Y$-objects equal those of $\mathcal A_{\mathbf G}(X)/\mathcal A_Z$, because $\mathcal A_Z\subset\mathcal A_S$ is full. So [separation](separation.md) gives bijectivity on morphisms, and the inverse is the inverse bijection. Strictness holds because $q$ commutes with transpose.

## Sources

- HS paper, Section 6

## Depends on

- [Quotient by a filtration](../../l-theory/base/categories/filtration-quotient.md)
- [Support subcategory](support-subcategory.md)

## Proof depends on

- [Separation](separation.md)
