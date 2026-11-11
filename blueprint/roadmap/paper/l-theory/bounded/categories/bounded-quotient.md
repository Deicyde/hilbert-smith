---
article_id: af_9c2350aa2a89afa35b40a51c
declaration: lemma
origin: cited
statement: formalized
proof: formalized
lean: HSP.Bounded.quotientEquiv
---

# Bounded quotients

For an involution-invariant Karoubi filtration $U\subset A$, the [entrywise quotient functor](bounded-quotient-functor.md) $C_\mathbb Z(A)/C_\mathbb Z(U)\to C_\mathbb Z(A/U)$ is a duality equivalence with identity unit and counit: it has a strict duality functor inverse, and both composites are identity functors.

*Proof sketch.* The functor is the identity on objects and reduces each entry mod $U$. It is full because each entry lifts and the lifted matrix keeps the same band. It is faithful because a bounded matrix whose entries all factor through $U$ factors through the degreewise splittings of [Bounded Karoubi filtrations](bounded-karoubi-filtration.md). It commutes with the duality entrywise.

## Sources

- [Carlsson-Pedersen 1995](../../../../../sources/paper/carlsson-pedersen-1995.md) [U]

## Depends on

- [Diagonal morphisms of $C_\mathbb Z(A)$](bounded-diag.md)
- [The entrywise quotient functor](bounded-quotient-functor.md)
- [The bounded subcategory is closed under sums and duals](bounded-sub-additive.md)
- [The bounded subcategory](bounded-sub.md)
- [Quotient by a subcategory](../../base/categories/filtration-quotient.md)
- [Bounded extension of a duality functor](bounded-functor.md)
- [Bounded Karoubi filtrations](bounded-karoubi-filtration.md)
- [Karoubi filtration](../../base/categories/karoubi-filtration.md)

## Proof depends on

- [Bounded Karoubi filtrations](bounded-karoubi-filtration.md)
- [Maps factoring through a subcategory](../../base/categories/filtration-ideal.md)
