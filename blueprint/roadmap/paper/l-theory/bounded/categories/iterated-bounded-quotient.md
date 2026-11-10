---
article_id: af_b40d77eea7d189a58471c2e3
declaration: def
origin: cited
---

# Iterated bounded quotients

Let $\mathcal U\subset\mathcal A$ be an involution-invariant Karoubi filtration, so that $C_{\mathbb Z^j}\mathcal U\subset C_{\mathbb Z^j}\mathcal A$ is one for every $j\ge0$ ([Iterated bounded filtrations](iterated-bounded-filtration.md)). Define $e_j:C_{\mathbb Z^j}\mathcal A/C_{\mathbb Z^j}\mathcal U\to C_{\mathbb Z^j}(\mathcal A/\mathcal U)$ by $e_0=\mathrm{id}$ and $e_{j+1}=C_\mathbb Z(e_j)\circ\tilde e_j$, where $\tilde e_j:C_\mathbb Z(C_{\mathbb Z^j}\mathcal A)/C_\mathbb Z(C_{\mathbb Z^j}\mathcal U)\to C_\mathbb Z(C_{\mathbb Z^j}\mathcal A/C_{\mathbb Z^j}\mathcal U)$ is the entrywise quotient functor of [Bounded quotients](bounded-quotient.md). Then $e_j$ is the identity on objects, bijective on morphisms, and a strict duality functor. So $e_j$ is an isomorphism of duality categories, and its inverse $e_j^{-1}$ is a strict duality functor.

*Proof sketch.* (Proof obligations.) Induction on $j$; for $j=0$, $e_0=\mathrm{id}$.
1. The first factor. By [Bounded quotients](bounded-quotient.md) for the filtration $C_{\mathbb Z^j}\mathcal U\subset C_{\mathbb Z^j}\mathcal A$, $\tilde e_j$ is the identity on objects, full, faithful and commutes with the duality on the nose.
2. The second factor. $C_\mathbb Z(e_j)$ applies $e_j$ entrywise ([Bounded extension of a duality functor](bounded-functor.md)). Since $e_j$ is the identity on objects and bijective on morphisms, so is $C_\mathbb Z(e_j)$: the entrywise inverse of a bounded matrix has the same propagation. It is strict because $e_j$ is.
3. A composite of two such functors is one.

## Sources

- [Carlsson-Pedersen 1995, §1](../../../../../sources/paper/carlsson-pedersen-1995.md) [U]
- New: the induction from the one-step statement.

## Depends on

- [Iterated bounded filtrations](iterated-bounded-filtration.md)
- [Bounded quotients](bounded-quotient.md)
- [Iterated bounded categories](iterated-bounded-category.md)
- [Quotient by a subcategory](../../base/categories/filtration-quotient.md)

## Proof depends on

- [Bounded quotients](bounded-quotient.md)
- [Bounded extension of a duality functor](bounded-functor.md)
