---
article_id: af_abc93f753910fd2f700c2849
declaration: lemma
origin: bridged
---

# Union formula

Let $(\mathcal U_A,\mathcal U_B)$ be an [excisive pair](excisive-pair.md) in $\mathcal A$ with $\mathcal U_Y=\mathcal U_A\cap\mathcal U_B$. Let $(P,\pi)$ be a strict $(k-1)$-dimensional symmetric Poincaré complex in $\mathrm{Kar}\,\mathcal U_Y$. Let $V_A=(f:iP\to D_A,\delta\phi_A,i_\%\pi)$ be a strict $k$-dimensional [$\mathcal U_Y$-pair](../../localization/boundary/u-pair.md) for $\mathcal U_Y\subset\mathcal U_A$, and $R=(g:iP\to D_B,\delta\phi_B,-i_\%\pi)$ a strict $k$-dimensional Poincaré pair in $\mathrm{Kar}\,\mathcal U_B$ with boundary $(P,-\pi)$, where each $i$ is the completion of the relevant inclusion. Through the inclusions $\mathrm{Kar}\,\mathcal U_Y\to\mathrm{Kar}\,\mathcal U_B$ and $\mathrm{Kar}\,\mathcal U_A\to\mathrm{Kar}\,\mathcal A$, $V_A$ is also a $\mathcal U_B$-pair for $\mathcal U_B\subset\mathcal A$; let $(V,\Phi)=(D_A\cup_PR,\Phi)$ be the [closed union](../../localization/boundary/closed-union.md) for $\mathcal U_B\subset\mathcal A$. Then
$$\partial_{A,B}\,\mathrm{cls}[V,\Phi]=\mathrm{cls}[P,\pi]\quad\text{in }\mathbb L_{k-1}(\mathcal U_Y),$$
where $\partial_{A,B}$ is the [excision boundary](excision-boundary.md).

*Proof sketch.* Write $q_BV_A$ for the [image](../../localization/boundary/image-pair.md) of $V_A$ modulo $\mathcal U_B$ and $q_YV_A$ for its image modulo $\mathcal U_Y$.
1. By [The closed union becomes the image of the pair](../../localization/boundary/union-image.md), the projection $p:q_BV\to q_BD_A$ is an isomorphism of complexes carrying $(q_B)_\%\Phi$ to $(q_B)_\%\delta\phi_A$. [Homotopy-isometry invariance](../../base/groups/homotopy-isometry-invariance.md) with $h=p$ and $\chi=0$ gives $(q_B)_*[V,\Phi]=\mathrm{fgt}[q_BV_A]$ in $L^p_k(\mathcal A/\mathcal U_B)$, with $\mathrm{fgt}$ [forgetting the decoration](../../localization/decorations/forget-decoration.md). By [The induced map commutes with cls](../groups/induced-map-cls.md), $(q_B)_*\mathrm{cls}[V,\Phi]=\mathrm{cls}\big(\mathrm{fgt}[q_BV_A]\big)$.
2. Since $e\circ q_Y=q_B\circ i_A$ as strict duality functors ([Excisive pair of filtrations](excisive-pair.md)), $e$ carries $q_YV_A$ to $q_BV_A$, structure included. So $\mathrm{fgt}[q_BV_A]=e_*\,\mathrm{fgt}[q_YV_A]$, and by [The induced map commutes with cls](../groups/induced-map-cls.md), $(q_B)_*\mathrm{cls}[V,\Phi]=e_*\,\mathrm{cls}\big(\mathrm{fgt}[q_YV_A]\big)$.
3. [Excision boundary of a preimage](excision-preimage.md) gives $\partial_{A,B}\,\mathrm{cls}[V,\Phi]=\partial\,\mathrm{cls}\big(\mathrm{fgt}[q_YV_A]\big)$, with $\partial$ the ultimate boundary of $\mathcal U_Y\subset\mathcal U_A$.
4. The [ultimate pair formula](pair-formula.md) for $\mathcal U_Y\subset\mathcal U_A$ gives $\mathrm{cls}[P,\pi]$.

## Sources

- HS paper, Section 6 (union boundary, sign $+1$)

## Depends on

- [Excisive pair of filtrations](excisive-pair.md)
- [Excision boundary](excision-boundary.md)
- [U-pairs](../../localization/boundary/u-pair.md)
- [Closing a pair by a null-cobordism of its boundary](../../localization/boundary/closed-union.md)

## Proof depends on

- [The closed union becomes the image of the pair](../../localization/boundary/union-image.md)
- [Image of a pair with boundary in Kar U](../../localization/boundary/image-pair.md)
- [Homotopy-isometry invariance](../../base/groups/homotopy-isometry-invariance.md)
- [Forgetting the decoration](../../localization/decorations/forget-decoration.md)
- [The induced map commutes with cls](../groups/induced-map-cls.md)
- [Excisive pair of filtrations](excisive-pair.md)
- [Excision boundary of a preimage](excision-preimage.md)
- [Ultimate pair formula](pair-formula.md)
