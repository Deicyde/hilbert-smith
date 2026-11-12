---
article_id: af_fe11d8948f9f721266108077
declaration: instance
origin: background
statement: formalized
lean: HSP.IsDecorated.isDualAdditive
---

# Decorated objects are closed under sums and duals

Let $\mathcal U\subset\mathcal A$ be a full additive subcategory with $\mathcal U^*\subset\mathcal U$. The [decorated objects](decorated-predicate.md) of $\mathrm{Kar}(\mathcal A/\mathcal U)$ form a [full additive subcategory closed under duality](../../base/categories/dual-additive-subcategory.md): they contain a zero object, a sum of any two of them, and the dual of each of them.

*Proof sketch.* (1) A zero object $Z$ has $[Z]=0=[q0]$. (2) $[M\oplus N]=[M]+[N]=[qQ]+[qQ']=[q(Q\oplus Q')]$, since $q$ is additive. (3) If $[M]=[qQ]$, [Equality in $K_0$](../../bounded/categories/k-zero-stable-equality.md) gives $M\oplus X\cong qQ\oplus X$ for an object $X$ of $\mathcal A/\mathcal U$. Dualizing, using the [dual of a binary sum](../../base/categories/sums/dual-biproduct.md) and that $q$ is strict, gives $M^*\oplus X^*\cong q(Q^*)\oplus X^*$, so $[M^*]=[q(Q^*)]$.

## Sources

- New: the closure properties, objectwise.

## Depends on

- [Decorated objects of the completed quotient](decorated-predicate.md)
- [Additive subcategory closed under duality](../../base/categories/dual-additive-subcategory.md)
- [Small Q-linear category with strict duality](../../base/categories/duality-category.md)

## Proof depends on

- [The quotient duality functor](../../base/categories/quotient-duality-functor.md)
- [The class of an object in $K_0$](../../bounded/categories/classes/k-zero-class.md)
- [Isomorphism classes of objects](../../bounded/categories/classes/iso-classes.md)
- [Equality in $K_0$](../../bounded/categories/k-zero-stable-equality.md)
- [Dual of a binary sum](../../base/categories/sums/dual-biproduct.md)
- [Completion of a duality functor](../../base/categories/karoubi-functor.md)
- [Quotient by a subcategory](../../base/categories/filtration-quotient.md)
- [Idempotent completion with duality](../../base/categories/karoubi-duality.md)
