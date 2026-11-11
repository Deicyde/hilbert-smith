---
article_id: af_b76c69b7f641cf43a318bc1a
declaration: theorem
origin: background
statement: formalized
lean: HSP.Lp.map_id
proof: formalized
---

# The identity on L^p

For a duality category $\mathcal A$, $(\mathrm{id}_{\mathcal A})_*=\mathrm{id}$ on $L^p_k(\mathcal A)$, where $F_*=(\mathrm{Kar}\,F)_*$ as in [Induced homomorphism](induced-map.md).

*Proof sketch.* The [completion](../categories/karoubi-functor.md) $\mathrm{Kar}(\mathrm{id}_{\mathcal A})$ has the same objects and maps as $\mathrm{id}_{\mathrm{Kar}\,\mathcal A}$, and its duality isomorphism at $(M,e)$ is $e^*=\mathrm{id}_{(M^*,e^*)}$. So the identity maps form a [unitary natural isomorphism](../categories/unitary-isomorphism.md) $\mathrm{id}_{\mathrm{Kar}\,\mathcal A}\cong\mathrm{Kar}(\mathrm{id}_{\mathcal A})$. Conclude by [unitary invariance](unitary-invariance.md) and [identity induces the identity](induced-map-id.md).

## Sources

- New: item 1 of [Functoriality on L^p](lp-functoriality.md), for the identity.

## Depends on

- [Induced homomorphism](induced-map.md)

## Proof depends on

- [Completion of a duality functor](../categories/karoubi-functor.md)
- [Unitary natural isomorphism](../categories/unitary-isomorphism.md)
- [Unitary invariance](unitary-invariance.md)
- [Identity induces the identity](induced-map-id.md)
