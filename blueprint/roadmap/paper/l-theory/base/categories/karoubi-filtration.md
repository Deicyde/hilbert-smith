---
article_id: af_a83e49c0f531729ffc39d5aa
declaration: def
origin: background
---

# Involution-invariant Karoubi filtration

Let $\mathcal U\subset\mathcal A$ be a full additive subcategory with $\mathcal U^*\subset\mathcal U$; closure under isomorphism is not required. A *$\mathcal U$-decomposition* of $M$ is an idempotent $p$ on $M$ such that $p$ splits through an object of $\mathcal U$ and $1-p$ splits: there are $E\in\mathcal U$, $M'$, and maps $i:E\to M$, $r:M\to E$, $i':M'\to M$, $r':M\to M'$ with $ri=1$, $ir=p$, $r'i'=1$, $i'r'=1-p$. Equivalently, $M\cong E\oplus M'$ and $p$ is the projection onto $E$. Order: $p\le p'$ iff $p'p=p=pp'$.

$\mathcal U$ is an *involution-invariant Karoubi filtration* of $\mathcal A$ if each object $M$ carries a nonempty set $\mathcal D(M)$ of $\mathcal U$-decompositions, directed under $\le$, such that:
1. (factorization) for every $g:V\to M$ with $V\in\mathcal U$ some $p\in\mathcal D(M)$ has $pg=g$, and for every $h:M\to V$ with $V\in\mathcal U$ some $p\in\mathcal D(M)$ has $hp=h$;
2. (duality) $p\in\mathcal D(M)$ iff $p^*\in\mathcal D(M^*)$.

Compatibility with sums follows: see [Filtrations are compatible with sums](karoubi-filtration-sums.md).

## Sources

- [Carlsson-Pedersen 1995, Def 1.27](../../../../../sources/paper/carlsson-pedersen-1995.md) [U]
- HS paper, Section 2 (the support filtrations split both pieces)

## Depends on

- [Small Q-linear category with strict duality](duality-category.md)
