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
- [Duality functor](../base/categories/duality-functor.md)
- [Additive subcategory closed under duality](../base/categories/dual-additive-subcategory.md)
- [Small Q-linear category with strict duality](../base/categories/duality-category.md)
- [Strict duality functor](../base/categories/duality-functors/strict-duality-functor.md)
