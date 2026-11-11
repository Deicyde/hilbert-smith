---
article_id: af_f13755f88ceae7ecbe7cd096
declaration: lemma
origin: background
---

# Forgetting after the decorated transition

Let $\mathcal U\subset\mathcal A$ be an involution-invariant Karoubi filtration and $e_{j+1}$ the isomorphism of [Iterated bounded quotients](../../bounded/categories/iterated-bounded-quotient.md). For all $j\ge0$ and $m$,
$$(e_{j+1})_*\circ\mathrm{fgt}\circ t^{\mathrm{im}}=t:\ L^p_m(C_{\mathbb Z^j}(\mathcal A/\mathcal U))\to L^p_{m+1}(C_{\mathbb Z^{j+1}}(\mathcal A/\mathcal U)),$$
where $t^{\mathrm{im}}$ is the [decorated transition](decorated-transition.md), $\mathrm{fgt}$ [forgets the decoration](../decorations/forget-decoration.md) and $t$ is the [transition map](transition-map.md) of $\mathcal A/\mathcal U$.

*Proof sketch.* $\mathrm{fgt}\,t^{\mathrm{im}}[C,\phi]$ is represented by $e_{j+1}^{-1}(C\otimes\Lambda)$ with structure $(e_{j+1}^{-1})_\%(\phi\otimes\lambda)$. Since $e_{j+1}e_{j+1}^{-1}=\mathrm{id}$ as strict duality functors, $(e_{j+1})_*$ of it is $[C\otimes\Lambda,\phi\otimes\lambda]=t[C,\phi]$, by [Functoriality on L^p](../../base/groups/lp-functoriality.md), item 1.

## Sources

- New: from the definitions.

## Depends on

- [Iterated bounded quotients](../../bounded/categories/iterated-bounded-quotient.md)
- [Forgetting the decoration](../decorations/forget-decoration.md)
- [Decorated transition](decorated-transition.md)
- [Transition map](transition-map.md)
- [Induced homomorphism](../../base/groups/induced-map.md)

## Proof depends on

- [Functoriality on L^p](../../base/groups/lp-functoriality.md)
