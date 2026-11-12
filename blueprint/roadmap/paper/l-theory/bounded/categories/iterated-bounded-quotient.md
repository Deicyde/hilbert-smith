---
article_id: af_b40d77eea7d189a58471c2e3
declaration: def
origin: cited
statement: formalized
lean: HSP.Bounded.powQuotientIso
---

# Iterated bounded quotients

Let $\mathcal U\subset\mathcal A$ be an involution-invariant Karoubi filtration, so that $C_{\mathbb Z^j}\mathcal U\subset C_{\mathbb Z^j}\mathcal A$ is one for every $j\ge0$ ([Iterated bounded filtrations](iterated-bounded-filtration.md)). The *iterated bounded quotient isomorphism* is the isomorphism of duality categories $e_j:C_{\mathbb Z^j}\mathcal A/C_{\mathbb Z^j}\mathcal U\to C_{\mathbb Z^j}(\mathcal A/\mathcal U)$ (a strict duality functor together with a strict duality functor inverse to it), defined by $e_0=\mathrm{id}$ and $e_{j+1}=C_\mathbb Z(e_j)\circ\tilde e_j$, where $\tilde e_j:C_\mathbb Z(C_{\mathbb Z^j}\mathcal A)/C_\mathbb Z(C_{\mathbb Z^j}\mathcal U)\to C_\mathbb Z(C_{\mathbb Z^j}\mathcal A/C_{\mathbb Z^j}\mathcal U)$ is the [entrywise quotient functor](bounded-quotient-functor.md), an isomorphism by [Bounded quotients](bounded-quotient.md).

*Proof sketch.* (Proof obligations: that $e_{j+1}$ and its inverse are strict and that both composites are identities.) Induction on $j$; for $j=0$, $e_0=\mathrm{id}$ is its own inverse. Suppose $e_j$ has the strict inverse $e_j^{-1}$.
1. The inverse. The [entrywise quotient functor](bounded-quotient-functor.md) $\tilde e_j$ [is strict](../bounded-quotient-functor-strict.md), and by [Bounded quotients](bounded-quotient.md) for the filtration $C_{\mathbb Z^j}\mathcal U\subset C_{\mathbb Z^j}\mathcal A$ it has a strict inverse $\tilde e_j^{-1}$. Put $e_{j+1}^{-1}=\tilde e_j^{-1}\circ C_\mathbb Z(e_j^{-1})$.
2. Strictness. $C_\mathbb Z(e_j)$ and $C_\mathbb Z(e_j^{-1})$ apply $e_j$ and $e_j^{-1}$ entrywise ([Bounded extension of a duality functor](bounded-functor.md)), so they are strict because $e_j$ and $e_j^{-1}$ are ([Bounded extensions of strict functors are strict](../bounded-functor-strict.md)); a composite of strict duality functors is strict.
3. The composites. Entrywise extension is functorial on the nose: $C_\mathbb Z(F)\circ C_\mathbb Z(G)=C_\mathbb Z(F\circ G)$ and $C_\mathbb Z(1)=1$. Hence $e_{j+1}^{-1}\circ e_{j+1}=\tilde e_j^{-1}\circ C_\mathbb Z(e_j^{-1}\circ e_j)\circ\tilde e_j=\tilde e_j^{-1}\circ\tilde e_j=1$, and likewise $e_{j+1}\circ e_{j+1}^{-1}=C_\mathbb Z(e_j)\circ C_\mathbb Z(e_j^{-1})=C_\mathbb Z(e_j\circ e_j^{-1})=1$.

**Remark (not formalized).** Each $e_j$ is the identity on the underlying families of objects.

## Sources

- [Carlsson-Pedersen 1995, §1](../../../../../sources/paper/carlsson-pedersen-1995.md) [U]
- New: the induction from the one-step statement.

## Depends on

- [The entrywise quotient functor](bounded-quotient-functor.md)
- [Iterated bounded subcategories are closed under sums and duals](iterated-bounded-sub-additive.md)
- [Iterated bounded subcategories](iterated-bounded-sub.md)
- [Iterated bounded filtrations](iterated-bounded-filtration.md)
- [Bounded quotients](bounded-quotient.md)
- [Iterated bounded categories](iterated-bounded-category.md)
- [Quotient by a subcategory](../../base/categories/filtration-quotient.md)
- [Bounded extension of a duality functor](bounded-functor.md)
- [Duality functor](../../base/categories/duality-functor.md)
- [The entrywise functor](entrywise-functor.md)

## Proof depends on

- [Bounded quotients](bounded-quotient.md)
- [Bounded extension of a duality functor](bounded-functor.md)
- [Bounded extensions of strict functors are strict](../bounded-functor-strict.md)
- [The entrywise quotient functor is strict](../bounded-quotient-functor-strict.md)
- [Identity and composite duality functors](../../base/categories/duality-functors/composite-duality-functor.md)
