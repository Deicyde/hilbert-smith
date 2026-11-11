---
article_id: af_5a641813d48392878502470b
declaration: class
origin: background
statement: formalized
lean: HSP.IsDualAdditive
---

# Additive subcategory closed under duality

Let $\mathcal A$ be a [duality category](duality-category.md). A full subcategory $\mathcal U\subset\mathcal A$, given by a property of the objects of $\mathcal A$, is a *full additive subcategory with $\mathcal U^*\subset\mathcal U$* if:

1. $\mathcal U$ contains a zero object;
2. for all $V,W\in\mathcal U$, some sum of $V$ and $W$ lies in $\mathcal U$: an object $P\in\mathcal U$ with maps $V\to P\to V$, $W\to P\to W$ making $P$ a biproduct of $V$ and $W$;
3. $V\in\mathcal U$ implies $V^*\in\mathcal U$.

Closure under isomorphism is not required, and the sum in (2) need not be the chosen sum of $\mathcal A$, which is determined only up to isomorphism.

## Sources

- Standard; the common hypothesis of the quotient by a subcategory and of involution-invariant Karoubi filtrations, split out so that both can cite it.

## Depends on

- [Small Q-linear category with strict duality](duality-category.md)
