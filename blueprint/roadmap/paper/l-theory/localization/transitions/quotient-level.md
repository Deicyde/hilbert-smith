---
article_id: af_5908dee28cc14018d0004da8
declaration: lemma
origin: background
---

# Quotient maps at each stage

Let $\mathcal U\subset\mathcal A$ be an involution-invariant Karoubi filtration, $q:\mathcal A\to\mathcal A/\mathcal U$ and $q^{(j)}:C_{\mathbb Z^j}\mathcal A\to C_{\mathbb Z^j}\mathcal A/C_{\mathbb Z^j}\mathcal U$ the quotient functors, and $e_j$ the isomorphism of [Iterated bounded quotients](../../bounded/categories/iterated-bounded-quotient.md). Then for all $j\ge0$ and $m$,
$$(e_j)_*\circ\mathrm{fgt}\circ q^{(j)}_*=(C_{\mathbb Z^j}q)_*:\ L^p_m(C_{\mathbb Z^j}\mathcal A)\to L^p_m(C_{\mathbb Z^j}(\mathcal A/\mathcal U)),$$
where $q^{(j)}_*$ is the [quotient map into the decorated group](../decorations/quotient-map.md) and $\mathrm{fgt}$ [forgets the decoration](../decorations/forget-decoration.md).

*Proof sketch.* (1) $e_j\circ q^{(j)}=C_{\mathbb Z^j}(q)$ as strict duality functors ([Iterated quotient functors](quotient-functor-level.md)). (2) [Forgetting after the quotient map](../decorations/forget-quotient.md) for the filtration $C_{\mathbb Z^j}\mathcal U\subset C_{\mathbb Z^j}\mathcal A$ gives $\mathrm{fgt}\circ q^{(j)}_*=(q^{(j)})_*$. (3) [Functoriality on L^p](../../base/groups/lp-functoriality.md), item 1, gives $(e_j)_*(q^{(j)})_*=(e_jq^{(j)})_*$.

## Sources

- New: from the definitions.

## Depends on

- [Iterated bounded quotients](../../bounded/categories/iterated-bounded-quotient.md)
- [Quotient map into the decorated group](../decorations/quotient-map.md)
- [Forgetting the decoration](../decorations/forget-decoration.md)
- [Induced homomorphism](../../base/groups/induced-map.md)

## Proof depends on

- [Iterated quotient functors](quotient-functor-level.md)
- [Forgetting after the quotient map](../decorations/forget-quotient.md)
- [Functoriality on L^p](../../base/groups/lp-functoriality.md)
