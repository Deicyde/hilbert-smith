---
article_id: af_537424e382be4638a43bd932
declaration: def
origin: cited
---

# Decorated quotient L-group

Let $\mathcal U\subset\mathcal A$ be a full additive subcategory, closed under isomorphism, with $\mathcal U^*\subset\mathcal U$, and let $q:\mathcal A\to\mathcal A/\mathcal U$ be the [quotient](../../base/categories/filtration-quotient.md). Write $q$ also for its [completion](../../base/categories/karoubi-functor.md) $\mathrm{Kar}\,q:\mathrm{Kar}\,\mathcal A\to\mathrm{Kar}(\mathcal A/\mathcal U)$. An object $M$ of $\mathrm{Kar}(\mathcal A/\mathcal U)$ is *decorated* if $[M]=[qQ]$ in [$K_0(\mathrm{Kar}(\mathcal A/\mathcal U))$](../../bounded/categories/k-zero.md) for some object $Q$ of $\mathrm{Kar}\,\mathcal A$.

Let $\mathrm{Dec}(\mathcal A/\mathcal U)\subset\mathrm{Kar}(\mathcal A/\mathcal U)$ be the full subcategory of decorated objects. It contains the zero objects and is closed under $\oplus$ and $*$, so with the duality of $\mathrm{Kar}(\mathcal A/\mathcal U)$ it is a [duality category](../../base/categories/duality-category.md). $L^{\mathrm{im}}_k(\mathcal A/\mathcal U)$ is the cobordism group of strict $k$-dimensional symmetric Poincaré complexes in $\mathrm{Dec}(\mathcal A/\mathcal U)$: the constructions of [Projective L-group](../../base/groups/l-group.md) and [Group structure on L^p](../../base/groups/l-group-add.md), with complexes and pairs whose chain objects are decorated.

*Proof sketch.* (Closure, the proof obligations of the subcategory.) (1) A zero object $Z$ has $[Z]=0=[q0]$. (2) $[M\oplus N]=[M]+[N]=[qQ]+[qQ']=[q(Q\oplus Q')]$, since $q$ is additive. (3) If $[M]=[qQ]$, [Equality in $K_0$](../../bounded/categories/k-zero-stable-equality.md) gives $M\oplus X\cong qQ\oplus X$ for an object $X$ of $\mathcal A/\mathcal U$. Dualizing, and using that $q$ is strict, gives $M^*\oplus X^*\cong q(Q^*)\oplus X^*$, so $[M^*]=[q(Q^*)]$.

**Remark (not formalized).** Ranicki's decorated groups $L^X$ restrict the Euler class of a complex to a subgroup $X$ of $K_0$. The decoration here restricts each chain object separately, which is what lifting needs.

## Sources

- [Ranicki 1992, decorated L-groups $L^X$](../../../../../sources/paper/ranicki-1992.md) [U], in an objectwise variant
- HS paper, Section 1

## Depends on

- [Quotient by a subcategory](../../base/categories/filtration-quotient.md)
- [Completion of a duality functor](../../base/categories/karoubi-functor.md)
- [$K_0$ of an idempotent completion](../../bounded/categories/k-zero.md)
- [Projective L-group](../../base/groups/l-group.md)
- [Group structure on L^p](../../base/groups/l-group-add.md)

## Proof depends on

- [Equality in $K_0$](../../bounded/categories/k-zero-stable-equality.md)
