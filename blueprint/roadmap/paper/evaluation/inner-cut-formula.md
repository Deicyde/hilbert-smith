---
article_id: af_764ce7a8f01377b16e8e2655
declaration: lemma
origin: bridged
---
# Inner cut formula

With the data of the [inner cut](inner-cut.md), let $(C,\psi)$ be a strict $k$-dimensional Poincaré complex in $\mathcal A_S$, let $(P\to D)$ be a strict Poincaré [pair](../l-theory/base/pairs/poincare-pair.md) with $D$ in $\mathcal A_B$ and $P$ in $\mathcal A_Y$, and let $\sigma\in\{\pm1\}$. Suppose that, eventually in each degree, the basis of $D_i$ is an invariant sub-basis of that of $C_i$ (inclusion $\iota$, projection $p$). Suppose also that the complementary basis is $A$-supported, that $pd_C\iota=d_D$, and that every nonzero entry of $p\psi p^*-\sigma\varphi_D$ has an endpoint label within $\eta_i\to0$ of $A$. Then $\partial^{\rm in}_{A,B}\mathrm{cls}[C,\psi]=\sigma\varepsilon_k\,\mathrm{cls}[P,\varphi_P]$, where $\varepsilon_k$ is the sign of the [pair formula](../l-theory/ultimate/boundary/pair-formula.md).

*Proof sketch.* Modulo $\mathcal A_A$ the complement is a zero object, so $p$ and $\iota$ are inverse isomorphisms. The defect $pd_C-d_Dp=pd_C(1-\iota p)$ factors through it, and $p\psi p^*=\sigma\varphi_D$ by the [support ideal](../categories/supports/support-ideal.md). By [homotopy-isometry invariance](../l-theory/base/groups/homotopy-isometry-invariance.md), the image of $\mathrm{cls}[C,\psi]$ is $\sigma\,\mathrm{cls}[D,\varphi_D]=\sigma e_*\mathrm{cls}[\bar D]$. Apply the [pair formula](../l-theory/ultimate/boundary/pair-formula.md).

## Sources
- HS paper, Section 6 (union boundary), applied on the inner side.
## Depends on
- [Inner cut](inner-cut.md), [Poincaré pair](../l-theory/base/pairs/poincare-pair.md)
## Proof depends on
- [Support ideal](../categories/supports/support-ideal.md), [homotopy-isometry invariance](../l-theory/base/groups/homotopy-isometry-invariance.md), [L-groups](../l-theory/base/groups/l-group.md), [pair formula](../l-theory/ultimate/boundary/pair-formula.md)
