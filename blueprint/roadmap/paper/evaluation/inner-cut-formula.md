---
article_id: af_764ce7a8f01377b16e8e2655
declaration: lemma
origin: bridged
---
# Inner cut formula

Let $A,B,Z\subseteq X$ be data as in the [cut boundary](../categories/cuts/cut-boundary.md), with $S=A\cup B$, $Y=A\cap B$ and $q_Z:\mathcal A_S\to\mathcal A_S/\mathcal A_Z$ the quotient functor. Let $(C,\psi)$ be a strict $k$-dimensional symmetric Poincaré complex in $\mathcal A_S$, let $\sigma\in\{\pm1\}$, and let $V$ be a strict $k$-dimensional [$\mathcal A_Y$-pair](../l-theory/localization/boundary/u-pair.md) for $\mathcal A_Y\subseteq\mathcal A_B$ over $(P,\pi)$, whose pair $(iP\to D,\delta\phi,i_\%\pi)$ is the image under the completion functors of a strict pair $(P\to D,\delta\phi,\pi)$ in $\mathcal A_B$ with $P$ in $\mathcal A_Y$. Suppose that, eventually in each degree, the basis of $D_r$ is an invariant sub-basis of that of $C_r$, with inclusion $\iota$ and projection $p$, that the complementary basis is $A$-supported, and that
$$p\,d_C\,\iota=d_D,\qquad p\,\psi\,p^*=\sigma\,\delta\phi .$$
Then
$$\partial_{A,B}\big((q_Z)_*\mathrm{cls}[C,\psi]\big)=-\sigma\,\mathrm{cls}[P,\pi]\quad\text{in }\mathbb L_{k-1}(\mathcal A_Y).$$

*Proof sketch.*
1. Let $q_A:\mathcal A_S\to\mathcal A_S/\mathcal A_A$ be the quotient functor. The complement of $D$ in $C$ is $A$-supported, so modulo $\mathcal A_A$ it is a zero object and $q_Ap$, $q_A\iota$ are inverse isomorphisms. The defect $pd_C-d_Dp=pd_C(1-\iota p)$ factors through the complement, so $q_Ap$ is an isomorphism of complexes, and it carries $(q_A)_\%\psi$ to $\sigma(q_A)_\%\delta\phi$ by the [support ideal](../categories/supports/support-ideal.md). [Homotopy-isometry invariance](../l-theory/base/groups/homotopy-isometry-invariance.md) and [the induced map commutes with cls](../l-theory/ultimate/groups/induced-map-cls.md) give $(q_A)_*\mathrm{cls}[C,\psi]=\sigma\,\mathrm{cls}[q_AD,(q_A)_\%\delta\phi]$.
2. Let $e:\mathcal A_B/\mathcal A_Y\to\mathcal A_S/\mathcal A_A$ be the excision functor of the [support excisive pair](../categories/supports/support-excisive-pair.md) $(\mathcal A_B,\mathcal A_A)$, and $q_Y$ the quotient functor of $\mathcal A_B$. Since $e\circ q_Y=q_A$ on $\mathcal A_B$ ([excisive pair](../l-theory/ultimate/boundary/excisive-pair.md)), $e$ carries the [image](../l-theory/localization/boundary/image-pair.md) $q_YV$ to $(q_AD,(q_A)_\%\delta\phi)$, so $(q_A)_*\mathrm{cls}[C,\psi]=e_*\big(\sigma\,\mathrm{cls}(\mathrm{fgt}[q_YV])\big)$, with $\mathrm{fgt}$ [forgetting the decoration](../l-theory/localization/decorations/forget-decoration.md).
3. [Excision boundary of a preimage](../l-theory/ultimate/boundary/excision-preimage.md) for $(\mathcal A_B,\mathcal A_A)$ and the [ultimate pair formula](../l-theory/ultimate/boundary/pair-formula.md) for $\mathcal A_Y\subseteq\mathcal A_B$ give $\partial_{B,A}\mathrm{cls}[C,\psi]=\sigma\,\partial\,\mathrm{cls}(\mathrm{fgt}[q_YV])=\sigma\,\mathrm{cls}[P,\pi]$.
4. [The cut boundary from the inner side](inner-cut.md) turns this into $\partial_{A,B}(q_Z)_*\mathrm{cls}[C,\psi]=-\sigma\,\mathrm{cls}[P,\pi]$.

## Sources
- HS paper, Section 6 (union boundary), applied on the side away from the exterior.
## Depends on
- [Cut boundary](../categories/cuts/cut-boundary.md), [U-pairs](../l-theory/localization/boundary/u-pair.md), [Poincaré pair](../l-theory/base/pairs/poincare-pair.md), [ultimate L-group and cls](../l-theory/ultimate/groups/ultimate-l-group.md)
## Proof depends on
- [Support ideal](../categories/supports/support-ideal.md), [homotopy-isometry invariance](../l-theory/base/groups/homotopy-isometry-invariance.md), [the induced map commutes with cls](../l-theory/ultimate/groups/induced-map-cls.md), [support excisive pair](../categories/supports/support-excisive-pair.md), [excisive pair](../l-theory/ultimate/boundary/excisive-pair.md), [image of a pair](../l-theory/localization/boundary/image-pair.md), [forgetting the decoration](../l-theory/localization/decorations/forget-decoration.md), [excision boundary of a preimage](../l-theory/ultimate/boundary/excision-preimage.md), [ultimate pair formula](../l-theory/ultimate/boundary/pair-formula.md), [the cut boundary from the inner side](inner-cut.md)
