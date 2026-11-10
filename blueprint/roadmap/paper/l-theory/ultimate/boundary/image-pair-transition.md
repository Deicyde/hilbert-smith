---
article_id: af_d986e0d1d4273a06e2534986
declaration: lemma
origin: background
---

# Decorated transition of an image pair

Let $\mathcal U\subset\mathcal A$ be an involution-invariant Karoubi filtration, $n\ge0$, $\mathcal U_n=C_{\mathbb Z^n}\mathcal U\subset C_{\mathbb Z^n}\mathcal A$ (an involution-invariant Karoubi filtration by [Iterated bounded quotients](../../bounded/categories/iterated-bounded-quotient.md), item 1), $q_n$ its quotient functor and $e_n$ the isomorphism of that article. Let $V=(f:iP\to D,\delta\phi,i_\%\pi)$ be a strict $k$-dimensional [$\mathcal U_n$-pair](../../localization/boundary/u-pair.md) over $(P,\pi)$. Let $u:i(P\otimes\Lambda)\to iP\otimes\Lambda$ be the isomorphism of propagation $0$ of [Duality functors commute with products](../../localization/products/functor-product.md) for the inclusion $\mathcal U\to\mathcal A$. Then
$$V\otimes\Lambda:=\big((f\otimes1)\circ u:i(P\otimes\Lambda)\to D\otimes\Lambda,\ \delta\phi\otimes\lambda,\ i_\%(\pi\otimes\lambda)\big)$$
is a strict $(k+1)$-dimensional $\mathcal U_{n+1}$-pair over $(P\otimes\Lambda,\pi\otimes\lambda)$, and
$$[q_{n+1}(V\otimes\Lambda)]=t^{\mathrm{im}}\big((e_n)_*\,\mathrm{fgt}\,[q_nV]\big)\quad\text{in }L^{\mathrm{im}}_{k+1}(C_{\mathbb Z^{n+1}}\mathcal A/C_{\mathbb Z^{n+1}}\mathcal U),$$
where $q_nV$ is the [image](../../localization/boundary/image-pair.md), $\mathrm{fgt}$ [forgets the decoration](../../localization/decorations/forget-decoration.md) and $t^{\mathrm{im}}$ is the [decorated transition](../../localization/transitions/decorated-transition.md).

*Proof sketch.*
1. The $\mathcal U_{n+1}$-pair. [Product of a pair with the line](../../localization/products/product-with-line.md) makes $(f\otimes1:iP\otimes\Lambda\to D\otimes\Lambda,\delta\phi\otimes\lambda,i_\%\pi\otimes\lambda)$ a strict $(k+1)$-dimensional pair in $\operatorname{Kar}C_{\mathbb Z^{n+1}}\mathcal A$, with no sign on the boundary. The inclusion is strict and $u_\%(i_\%(\pi\otimes\lambda))=i_\%\pi\otimes\lambda$, so [Transport of pairs along isomorphisms](../../base/pairs/pair-transport.md) ($s=1$) gives $V\otimes\Lambda$. Its boundary $(P\otimes\Lambda,\pi\otimes\lambda)$ is a strict Poincaré complex in $\operatorname{Kar}C_{\mathbb Z^{n+1}}\mathcal U$ by [Transition map](../../localization/transitions/transition-map.md), step 1.
2. The left side. By [Iterated quotient functors](../../localization/transitions/quotient-functor-level.md), $e_nq_n=C_{\mathbb Z^n}q$, so $(e_n)_*\,\mathrm{fgt}\,[q_nV]=[(C_{\mathbb Z^n}q)D,(C_{\mathbb Z^n}q)_\%\delta\phi]$, and $t^{\mathrm{im}}$ of it is represented by $e_{n+1}^{-1}\big((C_{\mathbb Z^n}q)D\otimes\Lambda\big)$ with the structure $(e_{n+1}^{-1})_\%\big((C_{\mathbb Z^n}q)_\%\delta\phi\otimes\lambda\big)$.
3. Comparison. [Duality functors commute with products](../../localization/products/functor-product.md) for $q$ gives an isomorphism $\omega:(C_{\mathbb Z^{n+1}}q)(D\otimes\Lambda)\to(C_{\mathbb Z^n}q)D\otimes\Lambda$ carrying $(C_{\mathbb Z^{n+1}}q)_\%(\delta\phi\otimes\lambda)$ to $(C_{\mathbb Z^n}q)_\%\delta\phi\otimes\lambda$. Since $C_{\mathbb Z^{n+1}}q=e_{n+1}q_{n+1}$, $e_{n+1}^{-1}(\omega)$ is an isomorphism from $q_{n+1}(D\otimes\Lambda)$ to the representative of step 2, carrying the structure of $q_{n+1}(V\otimes\Lambda)$ to that representative's structure.
4. Decorations. The chain objects of $q_{n+1}(D\otimes\Lambda)$ are images, hence [decorated](../../localization/decorations/decorated-object.md); those of the representative of step 2 are decorated by [Products with the line are decorated](../../localization/transitions/line-product-decorated.md). [Homotopy-isometric complexes are cobordant](../../base/pairs/cylinder-cobordism.md), with $\mathcal P$ the decorated objects and $\chi=0$, gives a cobordism in $\mathrm{Dec}$, so the classes agree.

## Sources

- New: from the definitions of $t^{\mathrm{im}}$ and of the image of a pair.

## Depends on

- [U-pairs](../../localization/boundary/u-pair.md)
- [Image of a pair with boundary in Kar U](../../localization/boundary/image-pair.md)
- [Duality functors commute with products](../../localization/products/functor-product.md)
- [Decorated transition](../../localization/transitions/decorated-transition.md)
- [Forgetting the decoration](../../localization/decorations/forget-decoration.md)
- [Iterated bounded quotients](../../bounded/categories/iterated-bounded-quotient.md)

## Proof depends on

- [Product of a pair with the line](../../localization/products/product-with-line.md)
- [Transport of pairs along isomorphisms](../../base/pairs/pair-transport.md)
- [Transition map](../../localization/transitions/transition-map.md)
- [Iterated quotient functors](../../localization/transitions/quotient-functor-level.md)
- [Duality functors commute with products](../../localization/products/functor-product.md)
- [Decorated objects](../../localization/decorations/decorated-object.md)
- [Products with the line are decorated](../../localization/transitions/line-product-decorated.md)
- [Homotopy-isometric complexes are cobordant](../../base/pairs/cylinder-cobordism.md)
