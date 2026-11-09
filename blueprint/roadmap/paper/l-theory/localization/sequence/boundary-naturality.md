---
article_id: af_2aeac9dce8c3153b0c0f291a
declaration: lemma
origin: background
---

# Naturality of the boundary

Let $\mathcal U\subset\mathcal A$ and $\mathcal U'\subset\mathcal A'$ be involution-invariant Karoubi filtrations, and let $(F,\xi):\mathcal A\to\mathcal A'$ be a duality functor with $FV\in\mathcal U'$ for every $V\in\mathcal U$. Let $F_{\mathcal U}:\mathcal U\to\mathcal U'$ be its restriction and $\bar F$ the [functor induced on quotients](induced-quotient-functor.md). Then
$$\partial'\circ\bar F^{\mathrm{im}}_*=(F_{\mathcal U})_*\circ\partial:L^{\mathrm{im}}_k(\mathcal A/\mathcal U)\to L^p_{k-1}(\mathcal U').$$

*Proof sketch.* Let $x\in L^{\mathrm{im}}_k(\mathcal A/\mathcal U)$. By [Lifting closed complexes](lift-to-pair-closed.md), $x=[qV]$ for a $\mathcal U$-pair $V=(f:iP\to D,\delta\phi,i_\%\pi)$. (1) By [Duality functors carry pairs to pairs](functor-pair.md), $(Ff,F_\%\delta\phi,F_\%i_\%\pi)$ is a strict pair in $\mathrm{Kar}\,\mathcal A'$. Since $\mathrm{Kar}\,F\circ i=i'\circ\mathrm{Kar}\,F_{\mathcal U}$ as duality functors, it is a $\mathcal U'$-pair $FV$ over $(F_{\mathcal U}P,(F_{\mathcal U})_\%\pi)$. (2) Since $\mathrm{Kar}\,\bar F\circ\mathrm{Kar}\,q=\mathrm{Kar}\,q'\circ\mathrm{Kar}\,F$, the image $q'(FV)$ equals $(\bar F(qD),\bar F_\%q_\%\delta\phi)$, so $[q'(FV)]=\bar F^{\mathrm{im}}_*x$, the map being defined by [Induced quotient functors keep decorations](induced-quotient-decorated.md). (3) The [pair formula](pair-formula.md) for $FV$ and for $V$ gives $\partial'\bar F^{\mathrm{im}}_*x=[F_{\mathcal U}P,(F_{\mathcal U})_\%\pi]=(F_{\mathcal U})_*[P,\pi]=(F_{\mathcal U})_*\partial x$.

## Sources

- New: a functor applied to a lift is a lift

## Depends on

- [Localization boundary](localization-boundary.md)
- [Functor induced on quotients](induced-quotient-functor.md)
- [Decorated induced map](decorated-induced-map.md)
- [Induced homomorphism](../../base/groups/induced-map.md)

## Proof depends on

- [Lifting closed complexes](lift-to-pair-closed.md)
- [Duality functors carry pairs to pairs](functor-pair.md)
- [Induced quotient functors keep decorations](induced-quotient-decorated.md)
- [Pair formula](pair-formula.md)
