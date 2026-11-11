---
article_id: af_b40d77eea7d189a58471c2e3
declaration: def
origin: cited
statement: formalized
lean: HSP.Bounded.powQuotientIso
---

# Iterated bounded quotients

Let $\mathcal U\subset\mathcal A$ be an involution-invariant Karoubi filtration, so that $C_{\mathbb Z^j}\mathcal U\subset C_{\mathbb Z^j}\mathcal A$ is one for every $j\ge0$ ([Iterated bounded filtrations](iterated-bounded-filtration.md)). The *iterated bounded quotient isomorphism* is the isomorphism of duality categories $e_j:C_{\mathbb Z^j}\mathcal A/C_{\mathbb Z^j}\mathcal U\to C_{\mathbb Z^j}(\mathcal A/\mathcal U)$ (a strict duality functor together with a strict duality functor inverse to it), defined by $e_0=\mathrm{id}$ and $e_{j+1}=C_\mathbb Z(e_j)\circ\tilde e_j$, where $\tilde e_j:C_\mathbb Z(C_{\mathbb Z^j}\mathcal A)/C_\mathbb Z(C_{\mathbb Z^j}\mathcal U)\to C_\mathbb Z(C_{\mathbb Z^j}\mathcal A/C_{\mathbb Z^j}\mathcal U)$ is the entrywise quotient functor of [Bounded quotients](bounded-quotient.md).

*Proof sketch.* (Proof obligations: that each composite is identity on objects, bijective on morphisms and strict, so that it has a strict inverse.) Induction on $j$; for $j=0$, $e_0=\mathrm{id}$.
1. The first factor. By [Bounded quotients](bounded-quotient.md) for the filtration $C_{\mathbb Z^j}\mathcal U\subset C_{\mathbb Z^j}\mathcal A$, $\tilde e_j$ is the identity on objects, full, faithful and commutes with the duality on the nose.
2. The second factor. $C_\mathbb Z(e_j)$ applies $e_j$ entrywise ([Bounded extension of a duality functor](bounded-functor.md)). Since $e_j$ is the identity on objects and bijective on morphisms, so is $C_\mathbb Z(e_j)$: the entrywise inverse of a bounded matrix has the same propagation. It is strict because $e_j$ is.
3. A composite of two such functors is one.

**Remark (not formalized).** Each $e_j$ is the identity on the underlying families of objects.

## Sources

- [Carlsson-Pedersen 1995, §1](../../../../../sources/paper/carlsson-pedersen-1995.md) [U]
- New: the induction from the one-step statement.

## Depends on

- [Iterated bounded subcategories are closed under sums and duals](iterated-bounded-sub-additive.md)
- [Iterated bounded subcategories](iterated-bounded-sub.md)
- [Iterated bounded filtrations](iterated-bounded-filtration.md)
- [Bounded quotients](bounded-quotient.md)
- [Iterated bounded categories](iterated-bounded-category.md)
- [Quotient by a subcategory](../../base/categories/filtration-quotient.md)
- [Bounded extension of a duality functor](bounded-functor.md)
- [Iterated bounded filtrations](iterated-bounded-filtration.md)
- [Duality functor](../../base/categories/duality-functor.md)

## Proof depends on

- [Bounded quotients](bounded-quotient.md)
- [Bounded extension of a duality functor](bounded-functor.md)
