---
article_id: af_fa03a63dffd07ea2872b89a7
declaration: lemma
origin: bridged
---

# Products

For duality categories $\mathcal A,\mathcal B$, with the componentwise duality on $\mathcal A\times\mathcal B$, the map $(\mathrm{pr}_{\mathcal A*},\mathrm{pr}_{\mathcal B*}):L^p_k(\mathcal A\times\mathcal B)\to L^p_k(\mathcal A)\oplus L^p_k(\mathcal B)$ is an isomorphism.

*Proof sketch.* (1) The inverse is $(x,y)\mapsto\iota_{\mathcal A*}x+\iota_{\mathcal B*}y$, where $\iota_{\mathcal A}:M\mapsto(M,0)$ is a non-strict duality functor with $\xi$ the unique isomorphism $0^*\cong0$ in the second slot, and likewise $\iota_{\mathcal B}$. (2) $\mathrm{pr}_{\mathcal A}\iota_{\mathcal A}=\mathrm{id}$, and $\mathrm{pr}_{\mathcal B}\iota_{\mathcal A}=0$, which induces $0$. (3) $\iota_{\mathcal A}\mathrm{pr}_{\mathcal A}\oplus\iota_{\mathcal B}\mathrm{pr}_{\mathcal B}\cong\mathrm{id}$ is unitary. Combine via [Sums of functors](sum-of-functors.md), [Unitary invariance](unitary-invariance.md) and [Functoriality of induced maps](induced-map-comp.md).

## Sources

- New: direct

## Depends on

- [Induced homomorphism](induced-map.md)

## Proof depends on

- [Sums of functors](sum-of-functors.md)
- [Unitary invariance](unitary-invariance.md)
- [Functoriality of induced maps](induced-map-comp.md)
