---
article_id: af_d986e0d1d4273a06e2534986
declaration: lemma
origin: background
---

# Decorated transition of an image pair

Let $\mathcal U\subset\mathcal A$ be an involution-invariant Karoubi filtration, $n\ge0$, and $V=(P\to D)$ a strict $k$-dimensional symmetric Poincaré pair in $\mathrm{Kar}\,C_{\mathbb Z^n}\mathcal A$ with $P$ in $\mathrm{Kar}\,C_{\mathbb Z^n}\mathcal U$. Let $V\otimes\Lambda$ be the strict $(k+1)$-dimensional pair of [Product with the line](../../localization/line/product-with-line.md), whose boundary $P\otimes\Lambda$ lies in $\mathrm{Kar}\,C_{\mathbb Z^{n+1}}\mathcal U$. Let $e_n:C_{\mathbb Z^n}\mathcal A/C_{\mathbb Z^n}\mathcal U\to C_{\mathbb Z^n}(\mathcal A/\mathcal U)$ be the equivalence of [Iterated bounded quotient](../../bounded/categories/iterated-bounded-quotient.md) for $n\ge1$, and the identity for $n=0$. Then
$$t^{\mathrm{im}}\big(e_{n*}\,\mathrm{forget}\,[\operatorname{im}V]\big)=[\operatorname{im}(V\otimes\Lambda)]\quad\text{in }L^{\mathrm{im}}_{k+1}(C_{\mathbb Z^{n+1}}\mathcal A/C_{\mathbb Z^{n+1}}\mathcal U),$$
where $\operatorname{im}$ is the [image of a pair](../../localization/sequence/image-pair.md).

*Proof sketch.* Write $q_n:C_{\mathbb Z^n}\mathcal A\to C_{\mathbb Z^n}\mathcal A/C_{\mathbb Z^n}\mathcal U$ for the quotient functor.
1. $e_n\circ q_n=C_{\mathbb Z^n}q$ and $e_{n+1}\circ q_{n+1}=C_{\mathbb Z^{n+1}}q$ ([Transition and quotient](../../localization/line/transition-quotient.md); trivial for $n=0$). So $e_n(\operatorname{im}V)\otimes\Lambda=(C_{\mathbb Z^n}q\,D)\otimes\Lambda$ with the image of the structure of $V$, tensored with that of $\Lambda$.
2. As in [Naturality of the transition](../../localization/line/transition-naturality.md), $(C_{\mathbb Z^n}q\,D)\otimes\Lambda\cong C_{\mathbb Z^{n+1}}q(D\otimes\Lambda)=e_{n+1}(\operatorname{im}(V\otimes\Lambda))$ by a unitary isomorphism carrying structures to structures, because the structure of $V\otimes\Lambda$ on $D\otimes\Lambda$ is the product structure.
3. Apply $e_{n+1}^{-1}$, whose composite with $e_{n+1}$ is the identity: the representative $e_{n+1}^{-1}(e_n(\operatorname{im}V)\otimes\Lambda)$ of the left side is unitarily isomorphic to $\operatorname{im}(V\otimes\Lambda)$. Both have decorated chain objects ([Decorated transition](../../localization/line/decorated-transition.md); the right side consists of images of objects of $\mathrm{Kar}\,C_{\mathbb Z^{n+1}}\mathcal A$). The [cylinder cobordism](../../base/pairs/cylinder-cobordism.md) with $\chi=0$ has decorated chain objects, so the classes agree.

## Sources

- New: from the definitions of $t^{\mathrm{im}}$ and of the image of a pair.

## Depends on

- [Image of a pair](../../localization/sequence/image-pair.md)
- [Product with the line](../../localization/line/product-with-line.md)
- [Decorated transition](../../localization/line/decorated-transition.md)
- [Forgetting the decoration](../../localization/sequence/forget-decoration.md)
- [Iterated bounded quotient](../../bounded/categories/iterated-bounded-quotient.md)

## Proof depends on

- [Transition and quotient](../../localization/line/transition-quotient.md)
- [Naturality of the transition](../../localization/line/transition-naturality.md)
- [Iterated bounded quotient](../../bounded/categories/iterated-bounded-quotient.md)
- [Homotopy-isometric complexes are cobordant](../../base/pairs/cylinder-cobordism.md)
- [Decorated quotient L-group](../../localization/sequence/decorated-l-group.md)
