---
article_id: af_74c9b2bbc7c5d04a9339250e
declaration: lemma
origin: bridged
---

# Cut formula

Let the data be as in the [cut boundary](cut-boundary.md), with $\mathcal Q=\mathcal A_S/\mathcal A_Z$ and the cut square $(\mathcal U_A,\mathcal U_B)$. Let $V_A=(P\to D_A,\delta\phi_A,\phi)$ be a strict $k$-dimensional symmetric [Poincaré pair](../../l-theory/base/pairs/poincare-pair.md) in [$\mathrm{Kar}\,\mathcal U_A$](../../l-theory/base/categories/kar-subcategory.md) and $V_B=(P\to D_B,\delta\phi_B,-\phi)$ one in $\mathrm{Kar}\,\mathcal U_B$, with common boundary $P$ in $\mathrm{Kar}\,\mathcal U_Y$, oriented as the boundary of $V_A$. Let $V=V_A\cup_PV_B$ be their [closed union](../../l-theory/base/pairs/gluing-closed.md) in $\mathrm{Kar}\,\mathcal Q$. Then
$$\partial_{A,B}\,\mathrm{cls}[V]=\sigma_*\,\mathrm{cls}[P,\phi]\quad\text{in }\mathbb L_{k-1}(\mathcal A_Y),$$
where $\sigma:\mathcal U_Y\to\mathcal A_Y$ is the inverse in [separated support](../supports/quotient-separation-iso.md).

**Remark (not formalized).** A Karoubi object $(M,e)$ of $\mathcal Q$ with $M$ $A$-supported lies in $\mathrm{Kar}\,\mathcal U_A$, since $e$ factors through $M$; likewise for $B$ and $Y$.

*Proof sketch.* The [union formula](../../l-theory/ultimate/boundary/union-formula.md) for the cut square gives $\partial^{\rm exc}_{A,B}\,\mathrm{cls}[V]=\mathrm{cls}[P,\phi]$ in $\mathbb L_{k-1}(\mathcal U_Y)$. Apply $\sigma_*$, which is the last step of the cut boundary.

## Sources

- HS paper, Section 6

## Depends on

- [Cut boundary](cut-boundary.md)
- [Poincaré pair](../../l-theory/base/pairs/poincare-pair.md)
- [Completion of a subcategory](../../l-theory/base/categories/kar-subcategory.md)
- [Closed gluing](../../l-theory/base/pairs/gluing-closed.md)

## Proof depends on

- [Union formula](../../l-theory/ultimate/boundary/union-formula.md)
