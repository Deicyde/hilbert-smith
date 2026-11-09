---
article_id: af_081f9a2fd218001c83ea8ff0
declaration: lemma
origin: bridged
---

# Ultimate pair formula

Let $\mathcal U\subset\mathcal A$ be an involution-invariant Karoubi filtration and $V=(P\to D,\delta\phi,\phi)$ a strict $k$-dimensional symmetric Poincaré pair in $\mathrm{Kar}\,\mathcal A$ with $P$ in $\mathrm{Kar}\,\mathcal U$. Then
$$\partial\,\mathrm{cls}\big(\mathrm{forget}\,[\operatorname{im}V]\big)=\mathrm{cls}[P,\phi]\quad\text{in }\mathbb L_{k-1}(\mathcal U),$$
where $\operatorname{im}V$ is the [image of the pair](../../localization/sequence/image-pair.md) and forget is [forgetting the decoration](../../localization/sequence/forget-decoration.md).

*Proof sketch.* Put $x=\mathrm{forget}[\operatorname{im}V]\in L^{\langle 0\rangle}_k(\mathcal A/\mathcal U)$.
1. By [The ultimate boundary at each level](ultimate-boundary-level.md) with $j=0$ and $\sigma_{k,0}=\eta_k$ ([Boundary sign](boundary-sign.md)), $\partial\,\mathrm{cls}\,x=\eta_k\,\iota_1\,\partial(t^{\mathrm{im}}x)$.
2. By [Decorated transition of an image pair](image-pair-transition.md) with $n=0$, $t^{\mathrm{im}}x=[\operatorname{im}(V\otimes\Lambda)]$.
3. By [Product with the line](../../localization/line/product-with-line.md), $V\otimes\Lambda$ is a strict $(k+1)$-dimensional pair with boundary $(P\otimes\Lambda,\eta_k\,\phi\otimes\phi_\Lambda)$ in $\mathrm{Kar}\,C_{\mathbb Z}\mathcal U$. The [pair formula](../../localization/sequence/pair-formula.md) gives $\partial[\operatorname{im}(V\otimes\Lambda)]=[P\otimes\Lambda,\eta_k\,\phi\otimes\phi_\Lambda]$, which is $\eta_k\,t[P,\phi]$ by [Negation in L^p](../../base/groups/l-group-neg.md) and the [transition map](../../localization/line/transition-map.md).
4. Since $\eta_k^2=1$, $\partial\,\mathrm{cls}\,x=\iota_1t[P,\phi]=\iota_0[P,\phi]=\mathrm{cls}[P,\phi]$ by [Levels are compatible with the transition](../groups/level-compatible.md).

## Sources

- HS paper, Section 6 (the boundary of a relative-pair representative is its boundary, with sign $+1$)
- [Carlsson-Pedersen 1995, proof of Thm 4.1](../../../../../sources/paper/carlsson-pedersen-1995.md) [U]
- New: the sign bookkeeping through $\eta_k$ and $\sigma_{k,0}$.

## Depends on

- [Ultimate boundary](ultimate-boundary.md)
- [Image of a pair](../../localization/sequence/image-pair.md)
- [Forgetting the decoration](../../localization/sequence/forget-decoration.md)

## Proof depends on

- [The ultimate boundary at each level](ultimate-boundary-level.md)
- [Boundary sign](boundary-sign.md)
- [Decorated transition of an image pair](image-pair-transition.md)
- [Product with the line](../../localization/line/product-with-line.md)
- [Pair formula](../../localization/sequence/pair-formula.md)
- [Negation in L^p](../../base/groups/l-group-neg.md)
- [Transition map](../../localization/line/transition-map.md)
- [Levels are compatible with the transition](../groups/level-compatible.md)
=== NOTE pair-formula (ultimate)
HSP.LTheory.ultBoundary_pair. The sign is +1 because σ_{k,0} = η_k cancels the η_k of Product with the line (`Int.units_mul_self`). HS paper lines 554-567. Lean gap: when η_k = -1, step 3 is LP.neg_class; when the line group fixes η ≡ 1, step 3 is definitional.
