---
article_id: af_da20b57f3aab6a4e526b9c7d
declaration: lemma
origin: bridged
---
# Evaluation at the cubical pinch

Let $n\ge1$, $R>0$ and $0<s<R/\sqrt n$, let $\kappa$ be the [cubical pinch](cubical-pinch.md) for $n$ and $s$, and let $\Delta_{\mathbf 1}$ be the [iterated cut](../corner/theorem/iterated-cut.md) for the cut sets of the [standing data](../corner/standing-data.md). Then
$$\Delta_{\mathbf 1}\mathfrak m_\kappa=\varepsilon\,q_*\mathrm{cls}[\mathbf P],\qquad\varepsilon=(-1)^{n(n+1)/2},$$
where $\mathfrak m_\kappa$ is the [labelled-model class](germ.md) and $\mathbf P\in\mathcal P_{\mathbf 1}$ is the constant sequence $(P,\varphi_P)$ in the [sequence category](../categories/asymptotic/point-sequence-category.md), with $q$ the quotient functor to the [point category](../categories/asymptotic/point-quotient.md).

*Proof sketch.* Label every cell $b$ by $\kappa(x_b)$, and let $Q^{(m)}_i$ be the [pinch faces](pinch-faces.md).
1. Put $E_0=(D_i,\varphi_i)_i$, the [labelled model](labelled-model.md), and $E_m=(\partial Q^{(m)}_i,\varphi_{\partial Q^{(m)}_i})_i$ for $1\le m\le n$. By [block duality](../chain-models/blocks/block-duality.md) (6) and [pinch labels](pinch-labels.md) (2), the block pairs $(\partial Q^{(m)}_i\to Q^{(m)}_i)_i$ form a strict $(N-m+1)$-dimensional pair in $\mathcal A_{B_m}$ with boundary $E_m$ in $\mathcal A_{Y_m}$. So $E_m$ is a strict $(N-m)$-dimensional Poincaré complex in $\mathcal A_{Y_m}$.
2. The first step of $\Delta_{\mathbf 1}$ is $d_1\circ j_*$, and $j$ composed with the quotient $\mathcal A_{\mathbf 1}(S^n)\to\mathcal B_{\mathbf 1,Z_0}(S^n)$ is the quotient functor $q_{Z_0}$ of $\mathcal A_{S^n}$; so $j_*\mathfrak m_\kappa=(q_{Z_0})_*\mathrm{cls}E_0$. Each later step is $d_m\circ q_*$ with $q=q_\varnothing$.
3. For $1\le m\le n$, the [inner cut formula](inner-cut-formula.md) applies to $C=E_{m-1}$ and the block pair of $Q^{(m)}_i$, with $\sigma_1=1$ and $\sigma_m=(-1)^{n-m+1}$ for $m\ge2$: for $m=1$ by [box restriction](box-restriction.md) and pinch labels (1); for $m\ge2$ by [face restriction](face-restriction.md), where the replaced arc is preceded by $n-m+1$ arcs, and pinch labels (3). So $d_m\big((q_{Z^0_m})_*\mathrm{cls}E_{m-1}\big)=-\sigma_m\,\mathrm{cls}E_m$.
4. $Q^{(n)}_i$ has one arc factor, so $E_n=(P,-\varphi_P)\oplus(P,\varphi_P)$, the summands sitting at the bottom and top vertex of the arc ([arc pair](../chain-models/blocks/arc-pair.md), $\varphi_C$). By pinch labels (4) the first is $y_-$-supported and the second $y_+$-supported. Modulo $\mathcal A_{y_-}$ the first summand is a zero object, so by [homotopy-isometry invariance](../l-theory/base/groups/homotopy-isometry-invariance.md) the [component projection](component-projection.md) sends $\mathrm{cls}E_n$ to the class of the second summand relabelled at $y_+$, which [forgetting labels](../categories/functors/forget-labels.md) sends to $q_*\mathrm{cls}[\mathbf P]$.
5. So $\Delta_{\mathbf 1}\mathfrak m_\kappa=\prod_{m=1}^n(-\sigma_m)\,q_*\mathrm{cls}[\mathbf P]$, and $\prod_{m=1}^n(-\sigma_m)=(-1)^n(-1)^{\sum_{m=2}^n(n-m+1)}=(-1)^{n+n(n-1)/2}=\varepsilon$.

## Sources
- HS paper, Section 12 (boundary evaluation). New: grid boxes and exact restriction.
## Depends on
- [Iterated cut](../corner/theorem/iterated-cut.md), [standing data](../corner/standing-data.md), [labelled-model class](germ.md), [cubical pinch](cubical-pinch.md), [cells of CP^2](../chain-models/grid/cp2-cells.md), [sequence category](../categories/asymptotic/point-sequence-category.md), [point category](../categories/asymptotic/point-quotient.md)
## Proof depends on
- [Labelled model](labelled-model.md), [pinch faces](pinch-faces.md), [inner cut formula](inner-cut-formula.md), [box restriction](box-restriction.md), [face restriction](face-restriction.md), [pinch labels](pinch-labels.md), [block duality](../chain-models/blocks/block-duality.md), [arc pair](../chain-models/blocks/arc-pair.md), [component projection](component-projection.md), [forgetting labels](../categories/functors/forget-labels.md), [homotopy-isometry invariance](../l-theory/base/groups/homotopy-isometry-invariance.md)
