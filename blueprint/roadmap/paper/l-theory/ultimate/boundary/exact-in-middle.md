---
article_id: af_75435f6af570426a8b8e4744
declaration: theorem
origin: cited
---

# Ultimate exactness in the middle

Let $\mathcal U\subset\mathcal A$ be an involution-invariant Karoubi filtration with inclusion $i:\mathcal U\to\mathcal A$ and quotient functor $q:\mathcal A\to\mathcal A/\mathcal U$. If $y\in\mathbb L_k(\mathcal A)$ and $q_*y=0$ in $\mathbb L_k(\mathcal A/\mathcal U)$, then $y=i_*u$ for some $u\in\mathbb L_k(\mathcal U)$.

*Proof sketch.*
1. By [Every element comes from a finite level](../groups/level-exhaustive.md), $y=\iota_ja$ with $a\in L^{\langle -j\rangle}_k(\mathcal A)$. By [The induced map at each level](../groups/induced-map-level.md), $\iota_j(C_{\mathbb Z^j}q)_*a=0$, so [Classes zero in the colimit](../groups/level-kernel.md) gives $m$ with $t^m(C_{\mathbb Z^j}q)_*a=0$. Put $n=j+m$ and $b=t^ma=[C,\phi]$. By [Naturality of the transition](../../localization/line/transition-naturality.md), $(C_{\mathbb Z^n}q)_*b=0$.
2. Regard $(C,\phi)$ as the strict pair $(0\to C)$ with structure $\phi$ and zero boundary. By the definitions of the [quotient map](../../localization/sequence/quotient-map.md), the [image of a pair](../../localization/sequence/image-pair.md) and [forgetting the decoration](../../localization/sequence/forget-decoration.md), together with $e_n\circ q_n=C_{\mathbb Z^n}q$ ([Transition and quotient](../../localization/line/transition-quotient.md); trivial for $n=0$) and [Functoriality of induced maps](../../base/groups/induced-map-comp.md), $(C_{\mathbb Z^n}q)_*b=e_{n*}\,\mathrm{forget}\,[\operatorname{im}(0\to C)]$ and $q_*(tb)=[\operatorname{im}(0\to C\otimes\Lambda)]$.
3. [Decorated transition of an image pair](image-pair-transition.md) gives $q_*(tb)=t^{\mathrm{im}}\big((C_{\mathbb Z^n}q)_*b\big)=t^{\mathrm{im}}(0)=0$ in $L^{\mathrm{im}}_{k+n+1}(C_{\mathbb Z^{n+1}}\mathcal A/C_{\mathbb Z^{n+1}}\mathcal U)$.
4. [Exactness in the middle](../../localization/sequence/exact-in-middle.md) for $C_{\mathbb Z^{n+1}}\mathcal U\subset C_{\mathbb Z^{n+1}}\mathcal A$ ([Bounded Karoubi filtrations](../../bounded/categories/bounded-karoubi-filtration.md)) gives $w$ with $tb=(C_{\mathbb Z^{n+1}}i)_*w$.
5. By [Levels are compatible with the transition](../groups/level-compatible.md) and [The induced map at each level](../groups/induced-map-level.md), $y=\iota_{n+1}t^{m+1}a=\iota_{n+1}(C_{\mathbb Z^{n+1}}i)_*w=i_*\iota_{n+1}w$. Take $u=\iota_{n+1}w$.

## Sources

- [Carlsson-Pedersen 1995, Thm 4.2, spectrum-level statement](../../../../../sources/paper/carlsson-pedersen-1995.md) [U]
- New: group-level reduction to the finite level; one extra transition makes the null-cobordism decorated.

## Depends on

- [Induced map on ultimate L](../groups/induced-map.md)

## Proof depends on

- [Every element comes from a finite level](../groups/level-exhaustive.md)
- [The induced map at each level](../groups/induced-map-level.md)
- [Classes zero in the colimit](../groups/level-kernel.md)
- [Naturality of the transition](../../localization/line/transition-naturality.md)
- [Quotient map](../../localization/sequence/quotient-map.md)
- [Image of a pair](../../localization/sequence/image-pair.md)
- [Forgetting the decoration](../../localization/sequence/forget-decoration.md)
- [Transition and quotient](../../localization/line/transition-quotient.md)
- [Functoriality of induced maps](../../base/groups/induced-map-comp.md)
- [Decorated transition of an image pair](image-pair-transition.md)
- [Exactness in the middle](../../localization/sequence/exact-in-middle.md)
- [Bounded Karoubi filtrations](../../bounded/categories/bounded-karoubi-filtration.md)
- [Levels are compatible with the transition](../groups/level-compatible.md)
=== NOTE exact-in-middle (ultimate)
HSP.LTheory.ult_exact_middle. Step 2's identification of q_*[C] with the class of the image of (0 → C) is `rfl` if image-pair specializes to the quotient map on closed pairs; otherwise it is a one-line lemma for the localization core. Step 2 also needs (0 → C) ⊗ Λ = (0 → C ⊗ Λ) with the product structure, which matches the definition of trans.
