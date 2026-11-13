---
article_id: af_63eddaa08d357a58fecb6188
declaration: lemma
origin: background
statement: formalized
lean: HSP.Bounded.quotientFunctor_isStrict
proof: formalized
---

# The entrywise quotient functor is strict

Let $U\subset A$ be a [full additive subcategory closed under duality](../base/categories/dual-additive-subcategory.md). The [entrywise quotient functor](categories/bounded-quotient-functor.md) $C_\mathbb Z(A)/C_\mathbb Z(U)\to C_\mathbb Z(A/U)$ is a strict [duality functor](../base/categories/duality-functor.md): it sends $M^*$ to the dual of its image of $M$, and its duality isomorphism at $M$ is the identity, for every object $M$.

*Proof sketch.* The functor is the identity on objects, and the dualities of $C_\mathbb Z(A)/C_\mathbb Z(U)$ and of $C_\mathbb Z(A/U)$ both take the entrywise dual of the underlying family of objects of $A$. Its duality isomorphism is the identity by definition.

## Sources

- [Carlsson-Pedersen 1995](../../../../sources/paper/carlsson-pedersen-1995.md) [U]

## Depends on

- [The entrywise quotient functor](categories/bounded-quotient-functor.md)
- [Additive subcategory closed under duality](../base/categories/dual-additive-subcategory.md)
- [Small Q-linear category with strict duality](../base/categories/duality-category.md)
- [Strict duality functor](../base/categories/duality-functors/strict-duality-functor.md)
- [Quotient by a subcategory](../base/categories/filtration-quotient.md)
- [The bounded category $C_\mathbb Z(A)$](categories/bounded-category.md)
- [The induced duality on $C_\mathbb Z(A)$](categories/bounded-duality.md)
- [The bounded subcategory is closed under sums and duals](categories/bounded-sub-additive.md)
- [The bounded subcategory](categories/bounded-sub.md)

## Proof depends on

- [Duality functor](../base/categories/duality-functor.md)
