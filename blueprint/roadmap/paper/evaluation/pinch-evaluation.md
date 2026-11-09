---
declaration: lemma
origin: bridged
---
# Evaluation at the cubical pinch

There is $\varepsilon\in\{\pm1\}$, depending only on $n$, with $\Delta_{\mathbf 1}\mathfrak m_\kappa=\varepsilon\,q_*\mathrm{cls}[\mathbf P]$. Here $\mathbf P\in\mathcal P_{\mathbf 1}$ is the constant sequence $(P,\varphi_P)$.

*Proof sketch.*
1. Let $E_0=(D_i,\varphi_i)$ and $E_m=(\partial Q^{(m)}_i\otimes P,\varphi_{\partial Q^{(m)}})$, labelled by $\kappa$. By [block duality](../chain-models/block-duality.md) and [pinch labels](pinch-labels.md) (2), $(\partial Q^{(m)}\to Q^{(m)})\otimes P$ is a strict pair in $\mathcal A_{B_m}$ with boundary in $\mathcal A_{Y_m}$.
2. For $1\le m\le n$, $E_{m-1}$ and $Q^{(m)}_i\otimes P$ satisfy the hypotheses of the [inner cut formula](inner-cut-formula.md) with $\sigma=1$: for $m=1$ by [box restriction](box-restriction.md) and pinch labels (1); for $m\ge2$ by [face restriction](face-restriction.md) and pinch labels (2), (3). So $\partial^{\rm in}_m\mathrm{cls}E_{m-1}=\varepsilon_{N-m+1}\mathrm{cls}E_m$.
3. $E_n=(P,-\varphi_P)\oplus(P,\varphi_P)$ at the two ends of $Q^{(n)}_i$, by [arc pair](../chain-models/arc-pair.md) ($\varphi_C$). By pinch labels (4) the second summand lies near $y_+$ and the first near $y_-$. So $\pi_+$ gives $\mathrm{cls}(P,\varphi_P)$ at $y_+$, and $\Phi$ gives $q_*\mathrm{cls}[\mathbf P]$.

Put $\varepsilon=\prod_{m=1}^n\varepsilon_{N-m+1}$.

## Sources
- HS paper, Section 12 (boundary evaluation). New: grid boxes and exact restriction.
## Depends on
- [Iterated cut](../corner/iterated-cut.md), [germ](germ.md), [cubical pinch](cubical-pinch.md), [cells of CP^2](../chain-models/cp2-cells.md)
## Proof depends on
- [Inner cut formula](inner-cut-formula.md), [box restriction](box-restriction.md), [face restriction](face-restriction.md), [pinch labels](pinch-labels.md), [block duality](../chain-models/block-duality.md), [A9](../l-theory/A9.md)
