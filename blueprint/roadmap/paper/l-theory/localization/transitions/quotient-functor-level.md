---
article_id: af_d103d1b9c6cd4768f25f435d
declaration: lemma
origin: background
---

# Iterated quotient functors

Let $\mathcal U\subset\mathcal A$ be an involution-invariant Karoubi filtration, $q:\mathcal A\to\mathcal A/\mathcal U$ and $q^{(j)}:C_{\mathbb Z^j}\mathcal A\to C_{\mathbb Z^j}\mathcal A/C_{\mathbb Z^j}\mathcal U$ the quotient functors, and $e_j$ the isomorphism of [Iterated bounded quotients](../../bounded/categories/iterated-bounded-quotient.md). Then $e_j\circ q^{(j)}=C_{\mathbb Z^j}(q)$ as strict duality functors, for every $j\ge0$.

*Proof sketch.* Induction on $j$; for $j=0$ both sides are $q$, since $e_0=\mathrm{id}$. With $\tilde e_j$ as in that article, $\tilde e_j\circ q^{(j+1)}=C_\mathbb Z(q^{(j)})$, because both are the identity on objects and reduce each entry. So $e_{j+1}q^{(j+1)}=C_\mathbb Z(e_j)C_\mathbb Z(q^{(j)})=C_\mathbb Z(e_jq^{(j)})=C_\mathbb Z(C_{\mathbb Z^j}q)$ by [Bounded extension of a duality functor](../../bounded/categories/bounded-functor.md).

## Sources

- New: from the definitions.

## Depends on

- [Iterated bounded quotients](../../bounded/categories/iterated-bounded-quotient.md)
- [Bounded extension of a duality functor](../../bounded/categories/bounded-functor.md)
- [Quotient by a subcategory](../../base/categories/filtration-quotient.md)

## Proof depends on

- [Bounded extension of a duality functor](../../bounded/categories/bounded-functor.md)
