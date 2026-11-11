---
article_id: af_492ddbb9905401244a9d6f94
declaration: theorem
origin: background
statement: formalized
lean: HSP.Lp.map_comp
proof: formalized
---

# Composites on L^p

For duality functors $F:\mathcal A\to\mathcal A'$ and $G:\mathcal A'\to\mathcal A''$, $(G\circ F)_*=G_*\circ F_*$ on $L^p_k(\mathcal A)$, where $F_*=(\mathrm{Kar}\,F)_*$ as in [Induced homomorphism](induced-map.md).

*Proof sketch.* Write $(F,\xi)$, $(G,\zeta)$. The [completions](../categories/karoubi-functor.md) $\mathrm{Kar}(G\circ F)$ and $\mathrm{Kar}\,G\circ\mathrm{Kar}\,F$ have the same objects $(GFM,GFe)$ and the same maps on morphisms. Their duality isomorphisms at $(M,e)$ are $\zeta_{FM}G(\xi_M)GF(e^*)$ and $\zeta_{FM}G((Fe)^*)G(\xi_MF(e^*))$, which agree because $(Fe)^*\xi_M=\xi_MF(e^*)$ by naturality of $\xi$ and $e^*$ is idempotent. So the identity maps form a [unitary natural isomorphism](../categories/unitary-isomorphism.md) between them. Conclude by [unitary invariance](unitary-invariance.md) and [functoriality of induced maps](induced-map-comp.md).

## Sources

- New: item 1 of [Functoriality on L^p](lp-functoriality.md), for composites.

## Depends on

- [Induced homomorphism](induced-map.md)

## Proof depends on

- [Completion of a duality functor](../categories/karoubi-functor.md)
- [Unitary natural isomorphism](../categories/unitary-isomorphism.md)
- [Unitary invariance](unitary-invariance.md)
- [Functoriality of induced maps](induced-map-comp.md)
