---
article_id: af_8f6e36af9939c8839b0f691f
declaration: lemma
origin: bridged
---

# Equivalence invariance

Let $(F,\xi):\mathcal A\to\mathcal B$ and $(G,\zeta):\mathcal B\to\mathcal A$ be duality functors, with unitary natural isomorphisms $\eta:\mathrm{id}_{\mathcal A}\cong G\circ F$ and $\varepsilon:F\circ G\cong\mathrm{id}_{\mathcal B}$ (composites carry the composite duality data). Then $F_*:L^p_k(\mathcal A)\to L^p_k(\mathcal B)$ is an isomorphism with inverse $G_*$. No triangle identities are needed.

*Proof sketch.* [Functoriality of induced maps](induced-map-comp.md), [Unitary invariance](unitary-invariance.md) for $\eta$ and $\varepsilon$, and [Identity induces the identity](induced-map-id.md) give $G_*F_*=\mathrm{id}$ and $F_*G_*=\mathrm{id}$.

## Sources

- New: functoriality plus unitary invariance

## Depends on

- [Induced homomorphism](induced-map.md)
- [Unitary natural isomorphism](../categories/unitary-isomorphism.md)

## Proof depends on

- [Functoriality of induced maps](induced-map-comp.md)
- [Unitary invariance](unitary-invariance.md)
- [Identity induces the identity](induced-map-id.md)
