---
article_id: af_74c9b2bbc7c5d04a9339250e
declaration: lemma
origin: bridged
---

# Cut formula

Let the data be as in the [cut boundary](cut-boundary.md), with $\mathcal Q=\mathcal A_S/\mathcal A_Z$, the [cut square](cut-square.md) $(\mathcal U_A,\mathcal U_B)$ and $\mathcal U_Y=\mathcal U_A\cap\mathcal U_B$. Let $(P,\pi)$ be a strict $(k-1)$-dimensional symmetric Poincaré complex in $\mathrm{Kar}\,\mathcal U_Y$, the [idempotent completion](../../l-theory/base/categories/karoubi-duality.md) of $\mathcal U_Y$, read as in [$\mathcal U$-pairs](../../l-theory/localization/boundary/u-pair.md). Let $V_A=(f:iP\to D_A,\delta\phi_A,i_\%\pi)$ be a strict $k$-dimensional [$\mathcal U_Y$-pair](../../l-theory/localization/boundary/u-pair.md) for $\mathcal U_Y\subset\mathcal U_A$, and $R=(g:iP\to D_B,\delta\phi_B,-i_\%\pi)$ a strict $k$-dimensional [Poincaré pair](../../l-theory/base/pairs/poincare-pair.md) in $\mathrm{Kar}\,\mathcal U_B$ with boundary $(P,-\pi)$, each $i$ the [completion](../../l-theory/base/categories/karoubi-functor.md) of the relevant inclusion. Regard $V_A$ as a $\mathcal U_B$-pair for $\mathcal U_B\subset\mathcal Q$ through the inclusions, and let $(V,\Phi)=(D_A\cup_PR,\Phi)$ be the [closed union](../../l-theory/localization/boundary/closed-union.md) for $\mathcal U_B\subset\mathcal Q$. Then
$$\partial_{A,B}\,\mathrm{cls}[V,\Phi]=\sigma_*\,\mathrm{cls}[P,\pi]\quad\text{in }\mathbb L_{k-1}(\mathcal A_Y),$$
where $\sigma:\mathcal U_Y\to\mathcal A_Y$ is the inverse in [separated support](../supports/quotient-separation-iso.md).

**Remark (not formalized).** A Karoubi object $(M,e)$ with $M$ $A$-supported is an object of $\mathrm{Kar}\,\mathcal U_A$; likewise for $B$ and $Y$. The completion of an inclusion identifies $\mathrm{Kar}\,\mathcal U_A$ with the full subcategory of [completion of a subcategory](../../l-theory/base/categories/kar-subcategory.md) (the Remark of $\mathcal U$-pairs), but the statement uses the idempotent completion, as the union formula does. The closed union is the base [closed gluing](../../l-theory/base/pairs/gluing-closed.md) of $V_A$ with $R$ after $R$ is transported onto the boundary $0\oplus iP$, with $0$ the zero complex.

*Proof sketch.* The [union formula](../../l-theory/ultimate/boundary/union-formula.md) for the excisive pair $(\mathcal U_A,\mathcal U_B)$ in $\mathcal Q$ gives $\partial^{\rm exc}_{A,B}\,\mathrm{cls}[V,\Phi]=\mathrm{cls}[P,\pi]$ in $\mathbb L_{k-1}(\mathcal U_Y)$, with sign $+1$. Apply $\sigma_*$, which is the last step of the cut boundary.

## Sources

- HS paper, Section 6

## Depends on

- [Cut boundary](cut-boundary.md)
- [Cut square](cut-square.md)
- [Idempotent completion with duality](../../l-theory/base/categories/karoubi-duality.md)
- [Completion of a duality functor](../../l-theory/base/categories/karoubi-functor.md)
- [U-pairs](../../l-theory/localization/boundary/u-pair.md)
- [Poincaré pair](../../l-theory/base/pairs/poincare-pair.md)
- [Closing a pair by a null-cobordism of its boundary](../../l-theory/localization/boundary/closed-union.md)
- [Separated support in a quotient](../supports/quotient-separation-iso.md)

## Proof depends on

- [Union formula](../../l-theory/ultimate/boundary/union-formula.md)
