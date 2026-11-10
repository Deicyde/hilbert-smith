---
article_id: af_ffa69776e1a7aa35cfa2ce92
declaration: lemma
origin: background
---

# Naturality of the ultimate boundary

Let $\mathcal U\subset\mathcal A$ and $\mathcal U'\subset\mathcal A'$ be involution-invariant Karoubi filtrations, $(F,\xi):\mathcal A\to\mathcal A'$ a duality functor with $FV\in\mathcal U'$ for every $V\in\mathcal U$, $F|_{\mathcal U}:\mathcal U\to\mathcal U'$ its restriction, and $\bar F:\mathcal A/\mathcal U\to\mathcal A'/\mathcal U'$ the [functor induced on quotients](../../localization/decorations/induced-quotient-functor.md). Then $\partial'\circ\bar F_*=(F|_{\mathcal U})_*\circ\partial:\mathbb L_k(\mathcal A/\mathcal U)\to\mathbb L_{k-1}(\mathcal U')$.

*Proof sketch.* Every element of the colimit comes from a finite level ([Every element comes from a finite level](../groups/level-exhaustive.md)); take $x\in L^{\langle -j\rangle}_k(\mathcal A/\mathcal U)$, and let $F^{(j+1)}$ be the functor induced on $C_{\mathbb Z^{j+1}}\mathcal A/C_{\mathbb Z^{j+1}}\mathcal U$ by $C_{\mathbb Z^{j+1}}F$.
1. By [The induced map at each level](../groups/induced-map-level.md) and [The ultimate boundary at each level](ultimate-boundary-level.md), $\partial'\bar F_*\iota_jx=\iota_{j+1}\,\partial'\big(t^{\mathrm{im}}(C_{\mathbb Z^j}\bar F)_*x\big)$.
2. By [Naturality of the decorated transition](../../localization/transitions/decorated-transition-naturality.md), this is $\iota_{j+1}\,\partial'(F^{(j+1)})^{\mathrm{im}}_*t^{\mathrm{im}}x$, the decorated induced map being defined by [Induced quotient functors keep decorations](../../localization/decorations/induced-quotient-decorated.md).
3. [Naturality of the boundary](../../localization/boundary/boundary-naturality.md) for $C_{\mathbb Z^{j+1}}F$ and the filtrations $C_{\mathbb Z^{j+1}}\mathcal U\subset C_{\mathbb Z^{j+1}}\mathcal A$, $C_{\mathbb Z^{j+1}}\mathcal U'\subset C_{\mathbb Z^{j+1}}\mathcal A'$ ([Iterated bounded quotients](../../bounded/categories/iterated-bounded-quotient.md), item 1), whose restriction is $C_{\mathbb Z^{j+1}}(F|_{\mathcal U})$, turns it into $\iota_{j+1}(C_{\mathbb Z^{j+1}}F|_{\mathcal U})_*\partial^{(j)}x$.
4. By the two level lemmas again, this is $(F|_{\mathcal U})_*\partial\iota_jx$.

## Sources

- New: levelwise.

## Depends on

- [Ultimate boundary](ultimate-boundary.md)
- [Functor induced on quotients](../../localization/decorations/induced-quotient-functor.md)
- [Induced map on ultimate L](../groups/induced-map.md)

## Proof depends on

- [Every element comes from a finite level](../groups/level-exhaustive.md)
- [The induced map at each level](../groups/induced-map-level.md)
- [The ultimate boundary at each level](ultimate-boundary-level.md)
- [Naturality of the decorated transition](../../localization/transitions/decorated-transition-naturality.md)
- [Induced quotient functors keep decorations](../../localization/decorations/induced-quotient-decorated.md)
- [Naturality of the boundary](../../localization/boundary/boundary-naturality.md)
- [Iterated bounded quotients](../../bounded/categories/iterated-bounded-quotient.md)
