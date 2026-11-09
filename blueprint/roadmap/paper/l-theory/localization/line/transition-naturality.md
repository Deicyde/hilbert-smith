---
article_id: af_b4b6570e9cced5c05462a455
declaration: lemma
origin: background
---

# Naturality of the transition

Let $F:\mathcal A\to\mathcal A'$ be a strict duality functor and $j\ge0$.
1. $t\circ(C_{\mathbb Z^j}F)_*=(C_{\mathbb Z^{j+1}}F)_*\circ t$ as maps $L^p_m(C_{\mathbb Z^j}\mathcal A)\to L^p_{m+1}(C_{\mathbb Z^{j+1}}\mathcal A')$.
2. Let $\mathcal U\subset\mathcal A$ and $\mathcal U'\subset\mathcal A'$ be involution-invariant Karoubi filtrations with $F(\mathcal U)\subset\mathcal U'$. Let $\bar F:\mathcal A/\mathcal U\to\mathcal A'/\mathcal U'$ and $F^{(j+1)}:C_{\mathbb Z^{j+1}}\mathcal A/C_{\mathbb Z^{j+1}}\mathcal U\to C_{\mathbb Z^{j+1}}\mathcal A'/C_{\mathbb Z^{j+1}}\mathcal U'$ be the strict duality functors induced by $F$ and $C_{\mathbb Z^{j+1}}F$. Then $t^{\mathrm{im}}\circ(C_{\mathbb Z^j}\bar F)_*=(F^{(j+1)})^{\mathrm{im}}_*\circ t^{\mathrm{im}}$, where $(F^{(j+1)})^{\mathrm{im}}_*$ is the [decorated induced map](../sequence/decorated-induced-map.md).

*Proof sketch.*
1. For $N$ in $\operatorname{Kar}C_{\mathbb Z^j}\mathcal A$ and $V$ in $C_\mathbb Z(\mathbb Q)$, the canonical isomorphisms $F(M^{\oplus d})\cong F(M)^{\oplus d}$ form an isomorphism $\omega:(C_{\mathbb Z^{j+1}}F)(N\boxtimes V)\cong(C_{\mathbb Z^j}F)(N)\boxtimes V$ of propagation $0$, natural in both variables and compatible with $\kappa$ and the duality, because $F$ is additive and strict. On $C\otimes\Lambda$ it is an isomorphism of complexes carrying $(C_{\mathbb Z^{j+1}}F)_\%(\phi\otimes\lambda)$ to $(C_{\mathbb Z^j}F)_\%\phi\otimes\lambda$ block by block, with the same signs. Conclude by [Homotopy-isometry invariance](../../base/groups/homotopy-isometry-invariance.md) with $\chi=0$.
2. $(F^{(j+1)})^{\mathrm{im}}_*$ is defined: $F^{(j+1)}q^{(j+1)}=q'^{(j+1)}C_{\mathbb Z^{j+1}}F$, so on $K_0$ it carries the image of $K_0(\operatorname{Kar}C_{\mathbb Z^{j+1}}\mathcal A)$ into that of $K_0(\operatorname{Kar}C_{\mathbb Z^{j+1}}\mathcal A')$. The functor equation $e'_{j+1}F^{(j+1)}=C_{\mathbb Z^{j+1}}(\bar F)\,e_{j+1}$ holds by induction on $j$, both sides reducing and applying $F$ entrywise; hence $F^{(j+1)}e_{j+1}^{-1}=e'^{-1}_{j+1}C_{\mathbb Z^{j+1}}(\bar F)$. Then $e'^{-1}_{j+1}(\omega)$ is a structure-preserving isomorphism from $F^{(j+1)}e_{j+1}^{-1}(C\otimes\Lambda)$ to $e'^{-1}_{j+1}((C_{\mathbb Z^j}\bar F)C\otimes\Lambda)$. Both ends have decorated chain objects ([Products with the line are decorated](line-product-decorated.md)), so the cobordism of [Homotopy-isometric complexes are cobordant](../../base/pairs/cylinder-cobordism.md) is decorated.

## Sources

- New: from the definitions.

## Depends on

- [Transition map](transition-map.md)
- [Decorated transition](decorated-transition.md)
- [Decorated induced map](../sequence/decorated-induced-map.md)
- [Bounded extension of a duality functor](../../bounded/categories/bounded-functor.md)
- [Duality functor](../../base/categories/duality-functor.md)

## Proof depends on

- [Homotopy-isometry invariance](../../base/groups/homotopy-isometry-invariance.md)
- [Homotopy-isometric complexes are cobordant](../../base/pairs/cylinder-cobordism.md)
- [Iterated bounded quotients](../../bounded/categories/iterated-bounded-quotient.md)
- [Products with the line are decorated](line-product-decorated.md)
