---
article_id: af_d13ab21d8e8275dec9fea023
declaration: def
origin: background
statement: formalized
lean: HSP.decTransition
---

# Decorated transition

Let $\mathcal U\subset\mathcal A$ be an involution-invariant Karoubi filtration, $j\ge0$ and $m\in\mathbb Z$. The *decorated transition*
$$t^{\mathrm{im}}:L^p_m(C_{\mathbb Z^j}(\mathcal A/\mathcal U))\to L^{\mathrm{im}}_{m+1}(C_{\mathbb Z^{j+1}}\mathcal A/C_{\mathbb Z^{j+1}}\mathcal U),\qquad[C,\phi]\mapsto\big[e_{j+1}^{-1}(C\otimes\Lambda),\ (e_{j+1}^{-1})_\%(\phi\otimes\lambda)\big],$$
is a well-defined homomorphism. Here the representative is the [decorated product with the line](decorated-line-product.md), with $e_{j+1}$ the iterated bounded quotient isomorphism, applied through its Karoubi extension.

*Proof sketch.* The representative $\big[e_{j+1}^{-1}(C\otimes\Lambda),(e_{j+1}^{-1})_\%(\phi\otimes\lambda)\big]$ is the [decorated product with the line](decorated-line-product.md). Its class does not depend on the representative by [The decorated transition respects cobordism](decorated-transition-cobordant.md), and the map is additive by [The decorated transition is additive](decorated-transition-sum.md).

## Sources

- [Ranicki 1992, §17, transfer of decorations along the line](../../../../../sources/paper/ranicki-1992.md) [U]
- New: decoration checked object by object.

## Depends on

- [Iterated bounded subcategories are closed under sums and duals](../../bounded/categories/iterated-bounded-sub-additive.md)
- [Iterated bounded subcategories](../../bounded/categories/iterated-bounded-sub.md)
- [Decorated quotient L-group](../decorations/decorated-l-group.md)
- [The projective L-group](../../base/groups/projective-l-group.md)
- [Additive subcategory closed under duality](../../base/categories/dual-additive-subcategory.md)
- [Small Q-linear category with strict duality](../../base/categories/duality-category.md)
- [Quotient by a subcategory](../../base/categories/filtration-quotient.md)
- [Involution-invariant Karoubi filtration](../../base/categories/karoubi-filtration.md)
- [Iterated bounded categories](../../bounded/categories/iterated-bounded-category.md)

## Proof depends on

- [Decorated product with the line](decorated-line-product.md)
- [L-group](../../base/groups/l-group.md)
- [The decorated transition respects cobordism](decorated-transition-cobordant.md)
- [The decorated transition is additive](decorated-transition-sum.md)
