---
article_id: af_18e521f2144d5d6775044148
declaration: lemma
origin: bridged
---

# Stable lifts through a Karoubi quotient

Let $U\subset A$ be a full additive subcategory with $U^*\subset U$, and let $q:\mathrm{Kar}\,A\to\mathrm{Kar}(A/U)$ be the [completion](../../base/categories/karoubi-functor.md) of the quotient functor. If an object $M$ of $\mathrm{Kar}(A/U)$ satisfies $[M]=[qQ_0]$ in $K_0(\mathrm{Kar}(A/U))$ for some object $Q_0$ of $\mathrm{Kar}\,A$, then $M\oplus qX\cong qQ$ for some object $X$ of $A$ and some object $Q$ of $\mathrm{Kar}\,A$.

*Proof sketch.* [Equality in $K_0$](k-zero-stable-equality.md) gives $M\oplus Y\cong qQ_0\oplus Y$ for an object $Y$ of $A/U$. Every object of $A/U$ is an object $X$ of $A$, with $Y=qX$. Take $Q=Q_0\oplus X$; $q$ is additive.

## Sources

- New: stable equality plus surjectivity on objects.

## Depends on

- [Quotient by a subcategory](../../base/categories/filtration-quotient.md)
- [Completion of a duality functor](../../base/categories/karoubi-functor.md)
- [$K_0$ of an idempotent completion](k-zero.md)

## Proof depends on

- [Equality in $K_0$](k-zero-stable-equality.md)
