---
article_id: af_275bd8e5950961764033f2ab
declaration: def
origin: background
statement: formalized
lean: HSP.IsDecorated
---

# Decorated objects of the completed quotient

Let $\mathcal U\subset\mathcal A$ be a full additive subcategory with $\mathcal U^*\subset\mathcal U$, and let $q:\mathcal A\to\mathcal A/\mathcal U$ be the [quotient](../../base/categories/filtration-quotient.md). Write $q$ also for its [completion](../../base/categories/karoubi-functor.md) $\mathrm{Kar}\,q:\mathrm{Kar}\,\mathcal A\to\mathrm{Kar}(\mathcal A/\mathcal U)$. An object $M$ of $\mathrm{Kar}(\mathcal A/\mathcal U)$ is *decorated* if $[M]=[qQ]$ in [$K_0(\mathrm{Kar}(\mathcal A/\mathcal U))$](../../bounded/categories/k-zero.md) for some object $Q$ of $\mathrm{Kar}\,\mathcal A$.

**Remark (not formalized).** Ranicki's decorated groups $L^X$ restrict the Euler class of a complex to a subgroup $X$ of $K_0$. The decoration here restricts each chain object separately, which is what lifting needs. It also asks for $[M]=[qQ]$ rather than for $[M]$ to lie in the image subgroup of $K_0(\mathrm{Kar}\,\mathcal A)\to K_0(\mathrm{Kar}(\mathcal A/\mathcal U))$, which allows differences $[qQ]-[qQ']$. The two conditions give isomorphic L-groups: stabilizing rel boundary, by adding the elementary complex $qQ'\xrightarrow{1}qQ'$ in degrees $r$ and $r+1$ and pushing the correction upward, turns image-decorated complexes and pairs into ones whose chain objects all have classes of the form $[qQ]$. So the localization theorem cited for the image decoration [U] applies to the groups defined here.

## Sources

- [Ranicki 1992, decorated L-groups $L^X$](../../../../../sources/paper/ranicki-1992.md) [U], in an objectwise variant
- HS paper, Section 1

## Depends on

- [Quotient by a subcategory](../../base/categories/filtration-quotient.md)
- [Additive subcategory closed under duality](../../base/categories/dual-additive-subcategory.md)
- [Small Q-linear category with strict duality](../../base/categories/duality-category.md)

## Proof depends on

- [Duality functor](../../base/categories/duality-functor.md)
- [Idempotent completion with duality](../../base/categories/karoubi-duality.md)
- [Completion of a duality functor](../../base/categories/karoubi-functor.md)
- [The quotient duality functor](../../base/categories/quotient-duality-functor.md)
- [The class of an object in $K_0$](../../bounded/categories/classes/k-zero-class.md)
- [$K_0$ of an idempotent completion](../../bounded/categories/k-zero.md)
