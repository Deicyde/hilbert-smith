---
article_id: af_aa7e416a5e4de880d7550064
declaration: def
origin: background
---

# Level boundary

Let $\mathcal U\subset\mathcal A$ be an involution-invariant Karoubi filtration and $j\ge0$. The *level boundary* is the homomorphism
$$\partial^{(j)}:=\partial\circ t^{\mathrm{im}}:L^{\langle -j\rangle}_k(\mathcal A/\mathcal U)\to L^{\langle -j-1\rangle}_{k-1}(\mathcal U),$$
where $t^{\mathrm{im}}$ is the [decorated transition](decorated-transition.md) at level $j$ and $\partial$ is the [localization boundary](../boundary/localization-boundary.md) of the filtration $C_{\mathbb Z^{j+1}}\mathcal U\subset C_{\mathbb Z^{j+1}}\mathcal A$ ([Iterated bounded filtrations](../../bounded/categories/iterated-bounded-filtration.md)). The degrees match: $t^{\mathrm{im}}$ goes from $L^p_{k+j}(C_{\mathbb Z^j}(\mathcal A/\mathcal U))$ to $L^{\mathrm{im}}_{k+j+1}$, and $\partial$ lands in $L^p_{k+j}(C_{\mathbb Z^{j+1}}\mathcal U)=L^{\langle -j-1\rangle}_{k-1}(\mathcal U)$.

## Sources

- [Carlsson-Pedersen 1995, §4, boundary on lower L-groups](../../../../../sources/paper/carlsson-pedersen-1995.md) [U]
- New: the composite.

## Depends on

- [Decorated transition](decorated-transition.md)
- [Localization boundary](../boundary/localization-boundary.md)
- [Lower L-group](../../ultimate/groups/lower-l-group.md)
- [Iterated bounded filtrations](../../bounded/categories/iterated-bounded-filtration.md)
