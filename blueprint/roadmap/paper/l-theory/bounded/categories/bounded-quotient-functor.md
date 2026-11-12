---
article_id: af_9032f16a360de96052796a0e
declaration: def
origin: background
statement: formalized
lean: HSP.Bounded.quotientFunctor
---

# The entrywise quotient functor

Let $U\subset A$ be a [full additive subcategory closed under duality](../../base/categories/dual-additive-subcategory.md), so that $C_\mathbb Z(U)\subset C_\mathbb Z(A)$ is one as well ([The bounded subcategory is closed under sums and duals](bounded-sub-additive.md)). The entrywise quotient functor $C_\mathbb Z(A)\to C_\mathbb Z(A/U)$ applies the [quotient functor](../../base/categories/filtration-quotient.md) $q:A\to A/U$ to every entry ([Bounded extension of a duality functor](bounded-functor.md)). It sends every map that factors through an object of $C_\mathbb Z(U)$ to zero, since each entry of such a map is a finite sum of maps factoring through objects of $U$. So it descends to the *entrywise quotient functor*
$$C_\mathbb Z(A)/C_\mathbb Z(U)\to C_\mathbb Z(A/U),$$
which is the identity on objects and sends the class of a bounded matrix $(f_{l,n})$ to the matrix $(qf_{l,n})$. It is additive and $\mathbb Q$-linear, and with the identity duality isomorphism it is a strict duality functor: it commutes with the duality on the nose, since $q$ does entrywise.

## Sources

- [Carlsson-Pedersen 1995](../../../../../sources/paper/carlsson-pedersen-1995.md) [U]

## Depends on

- [The bounded subcategory](bounded-sub.md)
- [The bounded subcategory is closed under sums and duals](bounded-sub-additive.md)
- [Quotient by a subcategory](../../base/categories/filtration-quotient.md)
- [Bounded extension of a duality functor](bounded-functor.md)
- [Additive subcategory closed under duality](../../base/categories/dual-additive-subcategory.md)
- [Duality functor](../../base/categories/duality-functor.md)
- [The entrywise functor](entrywise-functor.md)

## Proof depends on

- [Maps factoring through a dual-closed subcategory form an ideal](../../base/categories/filtration-ideal-closure.md)
- [Maps factoring through a subcategory](../../base/categories/filtration-ideal.md)
