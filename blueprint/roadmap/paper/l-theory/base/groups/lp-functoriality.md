---
article_id: af_218622e3f1b076e2c4fcb5f0
declaration: theorem
origin: bridged
---

# Functoriality on L^p

Let $\mathcal A,\mathcal A',\mathcal A''$ be duality categories, and let a duality functor $F:\mathcal A\to\mathcal A'$ act on $L^p_k$ by $F_*=(\mathrm{Kar}\,F)_*$, as in [Induced homomorphism](induced-map.md). Then:
1. $(G\circ F)_*=G_*\circ F_*$ for duality functors $F:\mathcal A\to\mathcal A'$, $G:\mathcal A'\to\mathcal A''$, and $(\mathrm{id}_{\mathcal A})_*=\mathrm{id}$ on $L^p_k(\mathcal A)$;
2. if $F,G:\mathcal A\to\mathcal A'$ are duality functors and there is a [unitary natural isomorphism](../categories/unitary-isomorphism.md) $F\cong G$, then $F_*=G_*$;
3. $(F\oplus G)_*=F_*+G_*$ for duality functors $F,G:\mathcal A\to\mathcal A'$, with $F\oplus G$ as in [Sums of functors](sum-of-functors.md);
4. if $F:\mathcal A\to\mathcal A'$ and $G:\mathcal A'\to\mathcal A$ are duality functors with unitary natural isomorphisms $\mathrm{id}_{\mathcal A}\cong G\circ F$ and $F\circ G\cong\mathrm{id}_{\mathcal A'}$, then $F_*:L^p_k(\mathcal A)\to L^p_k(\mathcal A')$ is an isomorphism with inverse $G_*$.

*Proof sketch.* Write $(F,\xi)$, $(G,\zeta)$.
1. $\mathrm{Kar}(G\circ F)$ and $\mathrm{Kar}\,G\circ\mathrm{Kar}\,F$ ([Completion of a duality functor](../categories/karoubi-functor.md)) have the same objects $(GFM,GFe)$ and the same maps on morphisms. Their duality isomorphisms at $(M,e)$ are $\zeta_{FM}G(\xi_M)GF(e^*)$ and $\zeta_{FM}G((Fe)^*)G(\xi_MF(e^*))$, which agree because $(Fe)^*\xi_M=\xi_MF(e^*)$ by naturality of $\xi$ and $e^*$ is idempotent. So the identity maps form a unitary natural isomorphism between them. Likewise $\mathrm{Kar}(\mathrm{id}_{\mathcal A})$ has duality isomorphism $e^*=\mathrm{id}_{(M^*,e^*)}$, so it is unitarily isomorphic to $\mathrm{id}_{\mathrm{Kar}\,\mathcal A}$.
2. A unitary $\eta:F\cong G$ gives $\mathrm{Kar}\,\eta$ with components $\eta_MF(e):(FM,Fe)\to(GM,Ge)$ and inverses $\eta_M^{-1}G(e)$. It is natural because $\eta$ is, and unitary because $\eta$ is and $\eta_MF(e)=G(e)\eta_M$.
3. $\mathrm{Kar}(F\oplus G)(M,e)=(FM\oplus GM,Fe\oplus Ge)$, and the canonical isomorphism to the sum $(FM,Fe)\oplus(GM,Ge)$ in $\mathrm{Kar}\,\mathcal A'$ is natural and unitary.
4. Apply [Functoriality of induced maps](induced-map-comp.md), [Identity induces the identity](induced-map-id.md), [Unitary invariance](unitary-invariance.md), [Sums of functors](sum-of-functors.md) and [Equivalence invariance](equivalence-invariance.md) to the completed functors, using steps 1-3 to supply their hypotheses and Unitary invariance to replace $\mathrm{Kar}(G\circ F)$, $\mathrm{Kar}(\mathrm{id})$ and $\mathrm{Kar}(F\oplus G)$ by $\mathrm{Kar}\,G\circ\mathrm{Kar}\,F$, $\mathrm{id}$ and $\mathrm{Kar}\,F\oplus\mathrm{Kar}\,G$.

## Sources

- New: transfer of the functoriality lemmas along idempotent completion

## Depends on

- [Induced homomorphism](induced-map.md)
- [Completion of a duality functor](../categories/karoubi-functor.md)
- [Unitary natural isomorphism](../categories/unitary-isomorphism.md)
- [Sums of functors](sum-of-functors.md)

## Proof depends on

- [Functoriality of induced maps](induced-map-comp.md)
- [Identity induces the identity](induced-map-id.md)
- [Unitary invariance](unitary-invariance.md)
- [Equivalence invariance](equivalence-invariance.md)
