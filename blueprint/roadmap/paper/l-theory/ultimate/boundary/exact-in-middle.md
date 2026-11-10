---
article_id: af_75435f6af570426a8b8e4744
declaration: theorem
origin: cited
---

# Ultimate exactness in the middle

Let $\mathcal U\subset\mathcal A$ be an involution-invariant Karoubi filtration with inclusion $i:\mathcal U\to\mathcal A$ and quotient functor $q:\mathcal A\to\mathcal A/\mathcal U$. If $y\in\mathbb L_k(\mathcal A)$ and $q_*y=0$ in $\mathbb L_k(\mathcal A/\mathcal U)$, then $y=i_*u$ for some $u\in\mathbb L_k(\mathcal U)$.

*Proof sketch.*
1. By [Every element comes from a finite stage](../groups/level-exhaustive.md), $y=\iota_ja$ with $a\in L^{\langle -j\rangle}_k(\mathcal A)$. By [The induced map at each stage](../groups/induced-map-level.md), $\iota_j(C_{\mathbb Z^j}q)_*a=0$, so [Classes zero in the colimit](../groups/level-kernel.md) gives $m$ with $t^m(C_{\mathbb Z^j}q)_*a=0$. Put $n=j+m$ and $b=t^ma=[C,\phi]$. By [Naturality of the transition](../../localization/transitions/transition-naturality.md), $(C_{\mathbb Z^n}q)_*b=0$.
2. Let $q_n$ be the quotient functor of $\mathcal U_n=C_{\mathbb Z^n}\mathcal U\subset C_{\mathbb Z^n}\mathcal A$, $e_n$ the isomorphism of [Iterated bounded quotients](../../bounded/categories/iterated-bounded-quotient.md), and $Z'$ a complex of zero objects in $\operatorname{Kar}C_{\mathbb Z^n}\mathcal U$ with zero structure. By [Closed complexes are pairs with zero boundary](../../localization/boundary/closed-pair.md), $V=(0:iZ'\to C,\phi,0)$ is a strict $(k+n)$-dimensional [$\mathcal U_n$-pair](../../localization/boundary/u-pair.md) over $(Z',0)$. Its [image](../../localization/boundary/image-pair.md) is $(q_nC,(q_n)_\%\phi)$, so $[q_nV]=q^{(n)}_*b$ by the definition of the [quotient map](../../localization/decorations/quotient-map.md), and $(e_n)_*\,\mathrm{fgt}\,[q_nV]=(C_{\mathbb Z^n}q)_*b=0$ by [Quotient maps at each stage](../../localization/transitions/quotient-level.md).
3. [Decorated transition of an image pair](../../localization/transitions/image-pair-transition.md) gives $[q_{n+1}(V\otimes\Lambda)]=t^{\mathrm{im}}(0)=0$. The pair $V\otimes\Lambda$ has $C\otimes\Lambda$ and $\phi\otimes\lambda$ as its target and structure, so its image is $(q_{n+1}(C\otimes\Lambda),(q_{n+1})_\%(\phi\otimes\lambda))$ and $q^{(n+1)}_*(t\,b)=[q_{n+1}(V\otimes\Lambda)]=0$ in $L^{\mathrm{im}}_{k+n+1}(C_{\mathbb Z^{n+1}}\mathcal A/C_{\mathbb Z^{n+1}}\mathcal U)$.
4. [Exactness in the middle](../../localization/boundary/exact-in-middle.md) for $C_{\mathbb Z^{n+1}}\mathcal U\subset C_{\mathbb Z^{n+1}}\mathcal A$ ([Bounded Karoubi filtrations](../../bounded/categories/bounded-karoubi-filtration.md)) gives $w$ with $tb=(C_{\mathbb Z^{n+1}}i)_*w$.
5. By [Stages are compatible with the transition](../groups/level-compatible.md) and [The induced map at each stage](../groups/induced-map-level.md), $y=\iota_{n+1}t^{m+1}a=\iota_{n+1}(C_{\mathbb Z^{n+1}}i)_*w=i_*\iota_{n+1}w$. Take $u=\iota_{n+1}w$.

## Sources

- [Carlsson-Pedersen 1995, Thm 4.2, spectrum-level statement](../../../../../sources/paper/carlsson-pedersen-1995.md) [U]
- New: group-level reduction to the finite stage; one extra transition makes the null-cobordism decorated.

## Depends on

- [Induced map on ultimate L](../groups/induced-map.md)

## Proof depends on

- [Iterated bounded quotients](../../bounded/categories/iterated-bounded-quotient.md)
- [Every element comes from a finite stage](../groups/level-exhaustive.md)
- [The induced map at each stage](../groups/induced-map-level.md)
- [Classes zero in the colimit](../groups/level-kernel.md)
- [Naturality of the transition](../../localization/transitions/transition-naturality.md)
- [Closed complexes are pairs with zero boundary](../../localization/boundary/closed-pair.md)
- [U-pairs](../../localization/boundary/u-pair.md)
- [Image of a pair with boundary in Kar U](../../localization/boundary/image-pair.md)
- [Quotient map into the decorated group](../../localization/decorations/quotient-map.md)
- [Quotient maps at each stage](../../localization/transitions/quotient-level.md)
- [Decorated transition of an image pair](../../localization/transitions/image-pair-transition.md)
- [Exactness in the middle](../../localization/boundary/exact-in-middle.md)
- [Bounded Karoubi filtrations](../../bounded/categories/bounded-karoubi-filtration.md)
- [Stages are compatible with the transition](../groups/level-compatible.md)
- [Forgetting the decoration](../../localization/decorations/forget-decoration.md)
