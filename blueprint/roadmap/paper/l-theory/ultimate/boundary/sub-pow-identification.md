---
article_id: af_5c24a5cc215998d9ee161a71
declaration: def
origin: background
statement: formalized
lean: HSP.Bounded.subPowIdent
---

# Iterated bounded categories of a subcategory

Let $\mathcal U\subset\mathcal A$ be a full additive subcategory closed under the duality, a duality category by [Duality category of a dual-closed subcategory](../../base/categories/dual-subcategory.md). For $j\ge0$ there is a duality functor
$$C_{\mathbb Z^j}\mathcal U\to C_{\mathbb Z^j}(\mathcal U)$$
from the full subcategory $C_{\mathbb Z^j}\mathcal U\subset C_{\mathbb Z^j}\mathcal A$ of [Iterated bounded filtrations](../../bounded/categories/iterated-bounded-filtration.md) to the [iterated bounded category](../../bounded/categories/iterated-bounded-category.md) of $\mathcal U$ itself. It is the identity for $j=0$. For $j+1$ it reads an object $(M_n)_n$ of $C_{\mathbb Z}(C_{\mathbb Z^j}\mathcal U)\subset C_{\mathbb Z}(C_{\mathbb Z^j}\mathcal A)$, all of whose entries lie in $C_{\mathbb Z^j}\mathcal U$, as an object of $C_{\mathbb Z}$ of the full subcategory $C_{\mathbb Z^j}\mathcal U$, with the same matrices, and then applies the [bounded extension](../../bounded/categories/bounded-functor.md) of the functor at level $j$.

*Proof sketch.* (Proof obligations.) Reading a family as one of objects of the full subcategory keeps the matrices, their propagation, composition, identities, sums and duals, so it is a duality functor with identity duality isomorphisms; composites of duality functors are duality functors.

## Sources

- New: bookkeeping between the two readings of $C_{\mathbb Z^j}\mathcal U$.

## Depends on

- [Iterated bounded subcategories are closed under sums and duals](../../bounded/categories/iterated-bounded-sub-additive.md)
- [The bounded subcategory is closed under sums and duals](../../bounded/categories/bounded-sub-additive.md)
- [The bounded subcategory](../../bounded/categories/bounded-sub.md)
- [Iterated bounded subcategories](../../bounded/categories/iterated-bounded-sub.md)
- [Duality category of a dual-closed subcategory](../../base/categories/dual-subcategory.md)
- [Iterated bounded filtrations](../../bounded/categories/iterated-bounded-filtration.md)
- [Iterated bounded categories](../../bounded/categories/iterated-bounded-category.md)
- [Bounded extension of a duality functor](../../bounded/categories/bounded-functor.md)
- [Bounded Karoubi filtrations](../../bounded/categories/bounded-karoubi-filtration.md)
