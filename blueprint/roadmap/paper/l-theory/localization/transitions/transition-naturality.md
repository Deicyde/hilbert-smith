---
article_id: af_b4b6570e9cced5c05462a455
declaration: lemma
origin: background
statement: formalized
lean: HSP.transitionMap_natural
---

# Naturality of the transition

Let $(F,\xi):\mathcal A\to\mathcal A'$ be a duality functor and $j\ge0$, and let $C_{\mathbb Z^j}F$ be its $j$-fold [iterated bounded extension](../../bounded/categories/bounded-functor-iter.md), with $\xi$ applied entrywise. Then
$$t\circ(C_{\mathbb Z^j}F)_*=(C_{\mathbb Z^{j+1}}F)_*\circ t:\ L^p_m(C_{\mathbb Z^j}\mathcal A)\to L^p_{m+1}(C_{\mathbb Z^{j+1}}\mathcal A').$$

*Proof sketch.* Let $x=[C,\phi]$. [Duality functors commute with products](../products/functor-product.md), with $E=\Lambda$ and $\theta=\lambda$, gives an isomorphism of complexes $\omega:(C_{\mathbb Z^{j+1}}F)(C\otimes\Lambda)\to(C_{\mathbb Z^j}F)C\otimes\Lambda$ carrying $(C_{\mathbb Z^{j+1}}F)_\%(\phi\otimes\lambda)$ to $(C_{\mathbb Z^j}F)_\%\phi\otimes\lambda$. [Homotopy-isometry invariance](../../base/groups/homotopy-isometry-invariance.md) with $h=\omega$ and $\chi=0$ gives $(C_{\mathbb Z^{j+1}}F)_*\,t\,x=t\,(C_{\mathbb Z^j}F)_*x$.

## Sources

- New: from the definitions.

## Depends on

- [Iterated bounded extension](../../bounded/categories/bounded-functor-iter.md)
- [Transition map](transition-map.md)
- [Duality functor](../../base/categories/duality-functor.md)
- [Induced homomorphism](../../base/groups/induced-map.md)
- [The projective L-group](../../base/groups/projective-l-group.md)
- [Small Q-linear category with strict duality](../../base/categories/duality-category.md)

## Proof depends on

- [Duality functors commute with products](../products/functor-product.md)
- [Homotopy-isometry invariance](../../base/groups/homotopy-isometry-invariance.md)
