---
article_id: af_8c1d2ce34052ee820d87c2bc
declaration: lemma
origin: background
---

# Naturality of the decorated transition

Let $\mathcal U\subset\mathcal A$ and $\mathcal U'\subset\mathcal A'$ be involution-invariant Karoubi filtrations, $(F,\xi):\mathcal A\to\mathcal A'$ a duality functor with $FV\in\mathcal U'$ for every $V\in\mathcal U$, and $j\ge0$. Let $\bar F:\mathcal A/\mathcal U\to\mathcal A'/\mathcal U'$ be the [functor induced on quotients](../decorations/induced-quotient-functor.md), and $F^{(j+1)}:C_{\mathbb Z^{j+1}}\mathcal A/C_{\mathbb Z^{j+1}}\mathcal U\to C_{\mathbb Z^{j+1}}\mathcal A'/C_{\mathbb Z^{j+1}}\mathcal U'$ the functor induced in the same way by $C_{\mathbb Z^{j+1}}F$. Then
$$t^{\mathrm{im}}\circ(C_{\mathbb Z^j}\bar F)_*=(F^{(j+1)})^{\mathrm{im}}_*\circ t^{\mathrm{im}}:\ L^p_m(C_{\mathbb Z^j}(\mathcal A/\mathcal U))\to L^{\mathrm{im}}_{m+1}(C_{\mathbb Z^{j+1}}\mathcal A'/C_{\mathbb Z^{j+1}}\mathcal U'),$$
where $t^{\mathrm{im}}$ is the [decorated transition](decorated-transition.md) and $(F^{(j+1)})^{\mathrm{im}}_*$ the [decorated induced map](../decorations/decorated-induced-map.md), defined by [Induced quotient functors keep decorations](../decorations/induced-quotient-decorated.md).

*Proof sketch.* Let $x=[C,\phi]$.
1. Hypotheses. $C_{\mathbb Z^{j+1}}F$ applies $F$ entrywise, so it carries $C_{\mathbb Z^{j+1}}\mathcal U$ into $C_{\mathbb Z^{j+1}}\mathcal U'$, and both are involution-invariant Karoubi filtrations ([Iterated bounded filtrations](../../bounded/categories/iterated-bounded-filtration.md)). So $F^{(j+1)}$ and its decorated induced map are defined.
2. Functor equation. $e'_{j+1}\circ F^{(j+1)}=C_{\mathbb Z^{j+1}}(\bar F)\circ e_{j+1}$ as duality functors by [Iterated induced quotient functors](induced-functor-level.md). Hence $F^{(j+1)}\circ e_{j+1}^{-1}=e'^{-1}_{j+1}\circ C_{\mathbb Z^{j+1}}(\bar F)$.
3. Comparison. [Duality functors commute with products](../products/functor-product.md) for $\bar F$, with $E=\Lambda$ and $\theta=\lambda$, gives an isomorphism $\omega:C_{\mathbb Z^{j+1}}\bar F(C\otimes\Lambda)\to(C_{\mathbb Z^j}\bar F\,C)\otimes\Lambda$ carrying structures to structures. By step 2, $e'^{-1}_{j+1}(\omega)$ is an isomorphism from $F^{(j+1)}e^{-1}_{j+1}(C\otimes\Lambda)$, a representative of the right side, to $e'^{-1}_{j+1}((C_{\mathbb Z^j}\bar F\,C)\otimes\Lambda)$, a representative of the left side, carrying structures to structures.
4. Decorations. Both ends have decorated chain objects ([Products with the line are decorated](line-product-decorated.md)). [Homotopy-isometric complexes are cobordant](../../base/pairs/cylinder-cobordism.md), with $\mathcal P$ the [decorated objects](../decorations/decorated-object.md) and $\chi=0$, gives a cobordism in $\mathrm{Dec}$, so the two classes agree in $L^{\mathrm{im}}$.

## Sources

- New: from the definitions of $t^{\mathrm{im}}$ and the decorated induced map.

## Depends on

- [Decorated transition](decorated-transition.md)
- [Duality functor](../../base/categories/duality-functor.md)
- [Functor induced on quotients](../decorations/induced-quotient-functor.md)
- [Decorated induced map](../decorations/decorated-induced-map.md)
- [Induced quotient functors keep decorations](../decorations/induced-quotient-decorated.md)
- [Bounded extension of a duality functor](../../bounded/categories/bounded-functor.md)

## Proof depends on

- [Iterated induced quotient functors](induced-functor-level.md)
- [Duality functors commute with products](../products/functor-product.md)
- [Products with the line are decorated](line-product-decorated.md)
- [Homotopy-isometric complexes are cobordant](../../base/pairs/cylinder-cobordism.md)
- [Decorated objects](../decorations/decorated-object.md)
- [Iterated bounded filtrations](../../bounded/categories/iterated-bounded-filtration.md)
- [Iterated bounded quotients](../../bounded/categories/iterated-bounded-quotient.md)
