---
article_id: af_fa03a63dffd07ea2872b89a7
declaration: lemma
origin: bridged
---

# Products

For duality categories $\mathcal A,\mathcal A'$, with the componentwise duality on $\mathcal A\times\mathcal A'$, the map $(\mathrm{pr}_*,\mathrm{pr}'_*):L^p_k(\mathcal A\times\mathcal A')\to L^p_k(\mathcal A)\oplus L^p_k(\mathcal A')$ induced by the projections is an isomorphism.

*Proof sketch.* (1) The inverse is $(x,y)\mapsto\iota_*x+\iota'_*y$, where $\iota:M\mapsto(M,0)$ is a non-strict duality functor with $\xi$ the unique isomorphism $0^*\cong0$ in the second slot, and likewise $\iota'$. (2) $\mathrm{pr}\circ\iota=\mathrm{id}$, and $\mathrm{pr}'\circ\iota$ is the zero functor, which induces $0$. (3) $\iota\circ\mathrm{pr}\oplus\iota'\circ\mathrm{pr}'\cong\mathrm{id}$ is unitary. Combine these on $L^p$ by [Functoriality on L^p](lp-functoriality.md) (composites, unitary invariance and sums).

## Sources

- New: direct

## Depends on

- [Induced homomorphism](induced-map.md)

## Proof depends on

- [Functoriality on L^p](lp-functoriality.md)
