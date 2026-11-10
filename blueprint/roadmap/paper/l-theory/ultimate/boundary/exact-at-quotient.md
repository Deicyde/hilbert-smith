---
article_id: af_624b6de0f77d03eeef63da8a
declaration: theorem
origin: cited
---

# Ultimate exactness at the quotient

Let $\mathcal U\subset\mathcal A$ be an involution-invariant Karoubi filtration with quotient functor $q:\mathcal A\to\mathcal A/\mathcal U$. If $z\in\mathbb L_k(\mathcal A/\mathcal U)$ has $\partial z=0$, then $z=q_*y$ for some $y\in\mathbb L_k(\mathcal A)$.

*Proof sketch.*
1. By [Every element comes from a finite level](../groups/level-exhaustive.md), $z=\iota_jx$ with $x\in L^{\langle -j\rangle}_k(\mathcal A/\mathcal U)$. By [The ultimate boundary at each level](ultimate-boundary-level.md), $\iota_{j+1}\partial^{(j)}x=\partial z=0$, so [Classes zero in the colimit](../groups/level-kernel.md) gives $m$ with $t^m\partial^{(j)}x=0$.
2. Applying [Transition commutes with the boundary](../../localization/transitions/transition-boundary-commute.md) $m$ times, $t^m\partial^{(j)}x=\partial^{(j+m)}t^mx$. Put $n=j+m+1$. So $\partial\big(t^{\mathrm{im}}t^mx\big)=0$ for the filtration $C_{\mathbb Z^n}\mathcal U\subset C_{\mathbb Z^n}\mathcal A$ ([Level boundary](../../localization/transitions/level-boundary.md), [Bounded Karoubi filtrations](../../bounded/categories/bounded-karoubi-filtration.md)).
3. [Exactness at the quotient](../../localization/boundary/exact-at-quotient.md) gives $y'\in L^p_{k+n}(C_{\mathbb Z^n}\mathcal A)$ with $t^{\mathrm{im}}t^mx=q^{(n)}_*y'$, where $q^{(n)}_*$ is the [quotient map](../../localization/decorations/quotient-map.md) into $L^{\mathrm{im}}_{k+n}(C_{\mathbb Z^n}\mathcal A/C_{\mathbb Z^n}\mathcal U)$.
4. Apply $(e_n)_*\circ\mathrm{fgt}$, with $e_n$ the isomorphism of [Iterated bounded quotients](../../bounded/categories/iterated-bounded-quotient.md) and $\mathrm{fgt}$ the map [forgetting the decoration](../../localization/decorations/forget-decoration.md). By [Forgetting after the decorated transition](../../localization/transitions/transition-quotient.md), the left side becomes $t^{m+1}x$. By [Quotient maps at each level](../../localization/transitions/quotient-level.md), the right side becomes $(C_{\mathbb Z^n}q)_*y'$.
5. By [Levels are compatible with the transition](../groups/level-compatible.md) and [The induced map at each level](../groups/induced-map-level.md), $z=\iota_nt^{m+1}x=\iota_n(C_{\mathbb Z^n}q)_*y'=q_*\iota_ny'$. Take $y=\iota_ny'$.

## Sources

- [Carlsson-Pedersen 1995, Thm 4.2, spectrum-level statement](../../../../../sources/paper/carlsson-pedersen-1995.md) [U]
- New: group-level reduction to the finite level.

## Depends on

- [Ultimate boundary](ultimate-boundary.md)
- [Induced map on ultimate L](../groups/induced-map.md)

## Proof depends on

- [Every element comes from a finite level](../groups/level-exhaustive.md)
- [The ultimate boundary at each level](ultimate-boundary-level.md)
- [Classes zero in the colimit](../groups/level-kernel.md)
- [Transition commutes with the boundary](../../localization/transitions/transition-boundary-commute.md)
- [Bounded Karoubi filtrations](../../bounded/categories/bounded-karoubi-filtration.md)
- [Exactness at the quotient](../../localization/boundary/exact-at-quotient.md)
- [Quotient map into the decorated group](../../localization/decorations/quotient-map.md)
- [Forgetting the decoration](../../localization/decorations/forget-decoration.md)
- [Iterated bounded quotients](../../bounded/categories/iterated-bounded-quotient.md)
- [Forgetting after the decorated transition](../../localization/transitions/transition-quotient.md)
- [Quotient maps at each level](../../localization/transitions/quotient-level.md)
- [Levels are compatible with the transition](../groups/level-compatible.md)
- [The induced map at each level](../groups/induced-map-level.md)
- [Level boundary](../../localization/transitions/level-boundary.md)
