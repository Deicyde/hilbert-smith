---
article_id: af_a8e1f282106a978b97a09a45
declaration: def
origin: background
---

# Decorated induced map

Let $\mathcal U\subset\mathcal A$ and $\mathcal U'\subset\mathcal A'$ be as in [Decorated objects](decorated-object.md), and let $(G,\xi):\mathcal A/\mathcal U\to\mathcal A'/\mathcal U'$ be a duality functor such that $\mathrm{Kar}\,G$ carries decorated objects to decorated objects. Then
$$G^{\mathrm{im}}_*:L^{\mathrm{im}}_k(\mathcal A/\mathcal U)\to L^{\mathrm{im}}_k(\mathcal A'/\mathcal U'),\qquad [C,\phi]\mapsto[GC,G_\%\phi],$$
is the [induced homomorphism](../../base/groups/induced-map.md) of the restriction $\mathrm{Dec}(\mathcal A/\mathcal U)\to\mathrm{Dec}(\mathcal A'/\mathcal U')$ of $\mathrm{Kar}\,G$.

*Proof sketch.* By hypothesis $\mathrm{Kar}\,G$ restricts to a functor between the full subcategories of decorated objects. With the restricted $\xi$ it is a duality functor, and [Induced homomorphism](../../base/groups/induced-map.md) applies.

## Sources

- New: the induced homomorphism, restricted to decorated complexes

## Depends on

- [Decorated quotient L-group](decorated-l-group.md)
- [Completion of a duality functor](../../base/categories/karoubi-functor.md)
- [Induced homomorphism](../../base/groups/induced-map.md)
- [Decorated objects](decorated-object.md)
