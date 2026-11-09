---
article_id: af_f13755f88ceae7ecbe7cd096
declaration: lemma
origin: background
---

# Transitions and quotients

Let $\mathcal U\subset\mathcal A$ be an involution-invariant Karoubi filtration, $q:\mathcal A\to\mathcal A/\mathcal U$ and $q^{(j)}:C_{\mathbb Z^j}\mathcal A\to C_{\mathbb Z^j}\mathcal A/C_{\mathbb Z^j}\mathcal U$ the quotient functors, and $e_j$ the isomorphism of [Iterated bounded quotients](../../bounded/categories/iterated-bounded-quotient.md). Write $q^{(j)}_*:L^p_m(C_{\mathbb Z^j}\mathcal A)\to L^{\mathrm{im}}_m(C_{\mathbb Z^j}\mathcal A/C_{\mathbb Z^j}\mathcal U)$ for the [quotient map](../sequence/quotient-map.md) and $\mathrm{fgt}$ for the map that [forgets the decoration](../sequence/forget-decoration.md). Then for all $j\ge0$ and $m$:
1. $(e_j)_*\circ\mathrm{fgt}\circ q^{(j)}_*=(C_{\mathbb Z^j}q)_*$ on $L^p_m(C_{\mathbb Z^j}\mathcal A)$;
2. $(e_{j+1})_*\circ\mathrm{fgt}\circ t^{\mathrm{im}}=t$ on $L^p_m(C_{\mathbb Z^j}(\mathcal A/\mathcal U))$, where $t$ is the [transition map](transition-map.md) of $\mathcal A/\mathcal U$.

*Proof sketch.*
1. The functors $e_j\circ q^{(j)}$ and $C_{\mathbb Z^j}(q)$ are equal, by induction on $j$: $\tilde e_j\circ q^{(j+1)}=C_\mathbb Z(q^{(j)})$ because both reduce each entry, so $e_{j+1}q^{(j+1)}=C_\mathbb Z(e_j)C_\mathbb Z(q^{(j)})=C_\mathbb Z(C_{\mathbb Z^j}q)$ by [Bounded extension of a duality functor](../../bounded/categories/bounded-functor.md). On representatives, $\mathrm{fgt}\circ q^{(j)}_*$ is the induced map of $q^{(j)}$. Then [Functoriality of induced maps](../../base/groups/induced-map-comp.md).
2. $\mathrm{fgt}\,t^{\mathrm{im}}[C,\phi]$ is represented by $e_{j+1}^{-1}(C\otimes\Lambda)$ with structure $(e_{j+1}^{-1})_\%(\phi\otimes\lambda)$. Since $e_{j+1}e_{j+1}^{-1}=\mathrm{id}$ as strict duality functors, $(e_{j+1})_*$ of it is $[C\otimes\Lambda,\phi\otimes\lambda]=t[C,\phi]$, by [Functoriality of induced maps](../../base/groups/induced-map-comp.md) and [Identity induces the identity](../../base/groups/induced-map-id.md).

## Sources

- New: from the definitions.

## Depends on

- [Iterated bounded quotients](../../bounded/categories/iterated-bounded-quotient.md)
- [Quotient map](../sequence/quotient-map.md)
- [Forgetting the decoration](../sequence/forget-decoration.md)
- [Decorated transition](decorated-transition.md)
- [Transition map](transition-map.md)
- [Induced homomorphism](../../base/groups/induced-map.md)

## Proof depends on

- [Bounded extension of a duality functor](../../bounded/categories/bounded-functor.md)
- [Functoriality of induced maps](../../base/groups/induced-map-comp.md)
- [Identity induces the identity](../../base/groups/induced-map-id.md)
