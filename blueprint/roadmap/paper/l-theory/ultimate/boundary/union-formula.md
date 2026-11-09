---
article_id: af_abc93f753910fd2f700c2849
declaration: lemma
origin: bridged
---

# Union formula

Let $(\mathcal U_A,\mathcal U_B)$ be an excisive pair in $\mathcal A$. Let $V_A=(P\to D_A,\delta\phi_A,\phi)$ be a strict $k$-dimensional symmetric Poincaré pair in $\mathrm{Kar}\,\mathcal U_A$ and $V_B=(P\to D_B,\delta\phi_B,-\phi)$ one in $\mathrm{Kar}\,\mathcal U_B$, with common boundary $P$ in $\mathrm{Kar}\,\mathcal U_Y$, oriented as the boundary of $V_A$. Let $V=V_A\cup_PV_B$ be their closed union in $\mathrm{Kar}\,\mathcal A$. Then
$$\partial_{A,B}\,\mathrm{cls}[V]=\mathrm{cls}[P,\phi]\quad\text{in }\mathbb L_{k-1}(\mathcal U_Y).$$

*Proof sketch.*
1. By [The induced map commutes with cls](../groups/induced-map-cls.md) and [A union modulo one side](union-quotient.md) (applied in $\mathrm{Kar}\,\mathcal A$, where $P$ and $D_B$ lie in $\mathrm{Kar}\,\mathcal U_B$), $(q_B)_*\mathrm{cls}[V]=\mathrm{cls}\big(\mathrm{forget}[\operatorname{im}_BV_A]\big)$, with $\operatorname{im}_B$ the [image of a pair](../../localization/sequence/image-pair.md) modulo $\mathcal U_B$.
2. Since $e\circ q_Y=q_B\circ i_A$ ([Excisive pair of filtrations](excisive-pair.md)), $e$ carries the image $\operatorname{im}_YV_A$ of $V_A$ modulo $\mathcal U_Y$ to $\operatorname{im}_BV_A$, structure included. So $\mathrm{forget}[\operatorname{im}_BV_A]=e_*\,\mathrm{forget}[\operatorname{im}_YV_A]$, and by [The induced map commutes with cls](../groups/induced-map-cls.md), $(q_B)_*\mathrm{cls}[V]=e_*\,\mathrm{cls}\big(\mathrm{forget}[\operatorname{im}_YV_A]\big)$.
3. [Excision boundary of a preimage](excision-preimage.md) gives $\partial_{A,B}\,\mathrm{cls}[V]=\partial\,\mathrm{cls}\big(\mathrm{forget}[\operatorname{im}_YV_A]\big)$, the ultimate boundary of $\mathcal U_Y\subset\mathcal U_A$.
4. The [ultimate pair formula](pair-formula.md) for $\mathcal U_Y\subset\mathcal U_A$ gives $\mathrm{cls}[P,\phi]$.

## Sources

- HS paper, Section 6 (union boundary, sign $+1$)

## Depends on

- [Excision boundary](excision-boundary.md)
- [Algebraic union](../../base/pairs/algebraic-union.md)
- [Closed gluing](../../base/pairs/gluing-closed.md)

## Proof depends on

- [The induced map commutes with cls](../groups/induced-map-cls.md)
- [A union modulo one side](union-quotient.md)
- [Image of a pair](../../localization/sequence/image-pair.md)
- [Excisive pair of filtrations](excisive-pair.md)
- [Excision boundary of a preimage](excision-preimage.md)
- [Ultimate pair formula](pair-formula.md)
