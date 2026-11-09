---
article_id: af_be4c5988cc33b7bbd14b3021
declaration: lemma
origin: background
---

# Naturality of the decorated transition

Let $\mathcal U\subset\mathcal A$ and $\mathcal U'\subset\mathcal A'$ be involution-invariant Karoubi filtrations and $F:\mathcal A\to\mathcal A'$ a duality functor with $F(\mathcal U)\subset\mathcal U'$. Write $\bar F:\mathcal A/\mathcal U\to\mathcal A'/\mathcal U'$ for the induced functor, and $\bar F_n:C_{\mathbb Z^n}\mathcal A/C_{\mathbb Z^n}\mathcal U\to C_{\mathbb Z^n}\mathcal A'/C_{\mathbb Z^n}\mathcal U'$ for the functor induced by $C_{\mathbb Z^n}F$. Then for every $x\in L^p_m(C_{\mathbb Z^j}(\mathcal A/\mathcal U))$,
$$t^{\mathrm{im}}\big((C_{\mathbb Z^j}\bar F)_*x\big)=(\bar F_{j+1})^{\mathrm{im}}_*\big(t^{\mathrm{im}}x\big)\quad\text{in }L^{\mathrm{im}}_{m+1}(C_{\mathbb Z^{j+1}}\mathcal A'/C_{\mathbb Z^{j+1}}\mathcal U').$$

*Proof sketch.* Let $x=[C,\phi]$.
1. The equivalence $e$ of [Iterated bounded quotient](../../bounded/categories/iterated-bounded-quotient.md) and its inverse are the identity on objects and act entrywise on morphisms, so $\bar F_{j+1}\circ e^{-1}=e'^{-1}\circ C_{\mathbb Z^{j+1}}\bar F$ as duality functors.
2. As in [Naturality of the transition](../../localization/line/transition-naturality.md), there is a unitary isomorphism $C_{\mathbb Z^{j+1}}\bar F(C\otimes\Lambda)\cong(C_{\mathbb Z^j}\bar F\,C)\otimes\Lambda$ carrying one structure to the other.
3. Steps 1 and 2 give a unitary isomorphism between representatives of the two sides. Both have decorated chain objects ([Decorated transition](../../localization/line/decorated-transition.md), and [Decorated induced map](../../localization/sequence/decorated-induced-map.md) for the right side). The [cylinder cobordism](../../base/pairs/cylinder-cobordism.md) of a unitary isomorphism, with $\chi=0$, has decorated chain objects, so the classes agree in $L^{\mathrm{im}}$.

## Sources

- New: from the definitions of $t^{\mathrm{im}}$ and $\bar F^{\mathrm{im}}_*$.

## Depends on

- [Decorated transition](../../localization/line/decorated-transition.md)
- [Decorated induced map](../../localization/sequence/decorated-induced-map.md)
- [Iterated bounded quotient](../../bounded/categories/iterated-bounded-quotient.md)

## Proof depends on

- [Iterated bounded quotient](../../bounded/categories/iterated-bounded-quotient.md)
- [Naturality of the transition](../../localization/line/transition-naturality.md)
- [Homotopy-isometric complexes are cobordant](../../base/pairs/cylinder-cobordism.md)
- [Decorated quotient L-group](../../localization/sequence/decorated-l-group.md)
