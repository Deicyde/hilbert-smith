---
article_id: af_d8fc7b5325afaf87dcce725a
declaration: def
origin: background
---

# Decorated objects

Let $\mathcal U\subset\mathcal A$ be a full additive subcategory, closed under isomorphism, with $\mathcal U^*\subset\mathcal U$, and let $q:\mathcal A\to\mathcal A/\mathcal U$ be the [quotient](../../base/categories/filtration-quotient.md). Write $q$ also for its [completion](../../base/categories/karoubi-functor.md) $\mathrm{Kar}\,q:\mathrm{Kar}\,\mathcal A\to\mathrm{Kar}(\mathcal A/\mathcal U)$. An object $M$ of $\mathrm{Kar}(\mathcal A/\mathcal U)$ is *decorated* if $[M]=[qQ]$ in [$K_0(\mathrm{Kar}(\mathcal A/\mathcal U))$](../../bounded/categories/k-zero.md) for some object $Q$ of $\mathrm{Kar}\,\mathcal A$. The full subcategory $\mathrm{Dec}(\mathcal A/\mathcal U)\subset\mathrm{Kar}(\mathcal A/\mathcal U)$ of decorated objects, with the duality of $\mathrm{Kar}(\mathcal A/\mathcal U)$, is a [duality category](../../base/categories/duality-category.md).

*Proof sketch.* (Closure, the proof obligations of the subcategory.) (1) A zero object $Z$ has $[Z]=0=[q0]$. (2) $[M\oplus N]=[M]+[N]=[qQ]+[qQ']=[q(Q\oplus Q')]$, since $q$ is additive. (3) If $[M]=[qQ]$, [Equality in $K_0$](../../bounded/categories/k-zero-stable-equality.md) gives $M\oplus X\cong qQ\oplus X$ for an object $X$ of $\mathcal A/\mathcal U$. Dualizing, and using that $q$ is strict, gives $M^*\oplus X^*\cong q(Q^*)\oplus X^*$, so $[M^*]=[q(Q^*)]$.

**Remark (not formalized).** Ranicki's decorated groups $L^X$ restrict the Euler class of a complex to a subgroup $X$ of $K_0$. The decoration here restricts each chain object separately, which is what lifting needs. It also asks for $[M]=[qQ]$ rather than for $[M]$ to lie in the image subgroup of $K_0(\mathrm{Kar}\,\mathcal A)\to K_0(\mathrm{Kar}(\mathcal A/\mathcal U))$, which allows differences $[qQ]-[qQ']$. The two conditions give isomorphic L-groups: stabilizing rel boundary, by adding the elementary complex $qQ'\xrightarrow{1}qQ'$ in degrees $r$ and $r+1$ and pushing the correction upward, turns image-decorated complexes and pairs into ones whose chain objects all have classes of the form $[qQ]$. So the localization theorem cited for the image decoration [U] applies to the groups defined here.

## Sources

- [Ranicki 1992, decorated L-groups $L^X$](../../../../../sources/paper/ranicki-1992.md) [U], in an objectwise variant
- HS paper, Section 1

## Depends on

- [Quotient by a subcategory](../../base/categories/filtration-quotient.md)
- [Completion of a duality functor](../../base/categories/karoubi-functor.md)
- [$K_0$ of an idempotent completion](../../bounded/categories/k-zero.md)
- [Duality category](../../base/categories/duality-category.md)

## Proof depends on

- [Equality in $K_0$](../../bounded/categories/k-zero-stable-equality.md)
