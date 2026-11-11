---
article_id: af_da20b57f3aab6a4e526b9c7d
declaration: theorem
origin: bridged
statement: formalized
lean: HSP.Evaluation.iterCut_pinch
---
# Evaluation at the cubical pinch

Let $n\ge1$, $R>0$ and $0<s<R/\sqrt n$, let $\kappa$ be the [cubical pinch](cubical-pinch.md) for $n$ and $s$, and let $\Delta_{\mathbf 1}$ be the [scalar iterated cut](../corner/theorem/scalar-iterated-cut.md) for $n$, $R$ and $s$, with the [cut sets](../corner/cut-sets.md) $A_m,B_m,Y_m$, $y_\pm$ for $n$ and $s$ and the [exterior](../corner/exterior.md) $Z_0$ for $n$ and $R$. Then
$$\Delta_{\mathbf 1}\mathfrak m_\kappa=\varepsilon\,q_*\mathrm{cls}[\mathbf P],\qquad\varepsilon=(-1)^{n(n+1)/2},$$
where $\mathfrak m_\kappa$ is the [labelled-model class](germ.md) and $\mathbf P\in\mathcal P_{\mathbf 1}$ is the [constant sequence](constant-cp2-sequence.md) $(P,\varphi_P)$ in the [sequence category](../categories/asymptotic/point-sequence-category.md), with $q$ the quotient functor to the [point category](../categories/asymptotic/point-quotient.md). The class $\mathfrak m_\kappa$ is formed from a local datum $A$ at the prime $p$, and the identity holds for every such $A$.

*Proof sketch.* Label every cell $b$ by $\kappa(x_b)$, and let $Q^{(m)}_i$ be the [pinch faces](pinch-faces.md).
1. Put $E_0=(D_i,\varphi_i)_i$, the [labelled model](labelled-model.md), and $E_m=(\partial Q^{(m)}_i,\varphi_{\partial Q^{(m)}_i})_i$ for $1\le m\le n$. By [block pairs in the asymptotic category](../chain-models/blocks/block-pair-asymptotic.md) for $X=S^n$ and [pinch labels](pinch-labels.md) (2), the block pairs $(\partial Q^{(m)}_i\to Q^{(m)}_i)_i$ form a strict $(N-m+1)$-dimensional pair in $\mathcal A_{B_m}$ with boundary $E_m$ in $\mathcal A_{Y_m}$. So $E_m$ is a strict $(N-m)$-dimensional Poincaré complex in $\mathcal A_{Y_m}$. Classes of these strict complexes are taken through the [Karoubi embedding](../l-theory/base/categories/karoubi-embedding.md) $M\mapsto(M,1)$, as in the definition of $\mathfrak m$.
2. The first step of $\Delta_{\mathbf 1}$ is $d_1\circ j_*$. The support subcategory $\mathcal A_{S^n}$ is $\mathcal A_{\mathbf 1}(S^n)$ itself, with the inclusion $\iota:\mathcal A_{S^n}\to\mathcal A_{\mathbf 1}(S^n)$ the identity ([support of the whole space](../categories/supports/support-whole.md)). So $j\circ q_{\mathcal B}\circ\iota=q_{Z_0}$ strictly, where $q_{\mathcal B}:\mathcal A_{\mathbf 1}(S^n)\to\mathcal B_{\mathbf 1,Z_0}(S^n)$ is the quotient of the [exterior quotient](../categories/supports/exterior-quotient.md) and $q_{Z_0}$ is the quotient functor of $\mathcal A_{S^n}$ by $\mathcal A_{Z_0}$: both are the identity on objects and send $u$ to its class. Regarding $E_0$ as a complex in $\mathcal A_{S^n}$ through $\iota$, [functoriality](../l-theory/ultimate/groups/induced-map-comp.md) gives $j_*\mathfrak m_\kappa=j_*q_{\mathcal B*}\iota_*\mathrm{cls}E_0=(q_{Z_0})_*\mathrm{cls}E_0$. Each later step is $d_m\circ q_*$ with $q=q_\varnothing$.
3. For $1\le m\le n$, the [inner cut formula](inner-cut-formula.md) applies to $C=E_{m-1}$ and the block pair of $Q^{(m)}_i$, with $\sigma_1=1$ and $\sigma_m=(-1)^{n-m+1}$ for $m\ge2$: for $m=1$ by [box restriction](box-restriction.md) and pinch labels (1); for $m\ge2$ by [face restriction](face-restriction.md), where the replaced arc is preceded by $n-m+1$ arcs, and pinch labels (3). So $d_m\big((q_{Z^0_m})_*\mathrm{cls}E_{m-1}\big)=-\sigma_m\,\mathrm{cls}E_m$.
4. $Q^{(n)}_i$ has one arc factor, so $E_n=(P,-\varphi_P)\oplus(P,\varphi_P)$, the summands sitting at the bottom and top vertex of the arc ([arc pair](../chain-models/blocks/arc-pair.md), $\varphi_C$). By pinch labels (4) the first, $E_-$, is $y_-$-supported and the second, $E_+$, is $y_+$-supported. Follow the five steps of the [scalar component projection](scalar-component-projection.md). Modulo $\mathcal A_{\{y_-\}}$ the summand $E_-$ is a zero object, so by [homotopy-isometry invariance](../l-theory/base/groups/homotopy-isometry-invariance.md) the quotient sends $\mathrm{cls}E_n$ to the class of $E_+$. As $E_+$ lies in $\mathcal A_{\{y_+\}}$ and the excision $e$ and the quotient isomorphism $q'$ by $\mathcal A_\varnothing$ are induced by the identity on objects and matrices, the next two steps give $\mathrm{cls}E_+$ in $\mathbb L_{4}(\mathcal A_{\{y_+\}})$. The relabelling $R$ is inverse to $P$ on ultimate L ([relabelling equivalence](../categories/functors/relabelling-equivalence.md), [equivalence invariance](../l-theory/ultimate/groups/equivalence-invariance.md)), so the fourth step gives $\mathrm{cls}\,R(E_+)$, and [forgetting labels](../categories/functors/forget-labels.md) sends it to $q_*\mathrm{cls}[\mathbf P]$, since $\Phi R(E_+)$ is the constant sequence $(P,\varphi_P)$.
5. So $\Delta_{\mathbf 1}\mathfrak m_\kappa=\prod_{m=1}^n(-\sigma_m)\,q_*\mathrm{cls}[\mathbf P]$, and $\prod_{m=1}^n(-\sigma_m)=(-1)^n(-1)^{\sum_{m=2}^n(n-m+1)}=(-1)^{n+n(n-1)/2}=\varepsilon$.

## Sources
- HS paper, Section 12 (boundary evaluation). New: grid boxes and exact restriction.
## Depends on
- [The constant sequence of CP^2](constant-cp2-sequence.md)
- [Scalar iterated cut](../corner/theorem/scalar-iterated-cut.md)
- [The cut sets](../corner/cut-sets.md)
- [The exterior](../corner/exterior.md)
- [Labelled-model class](germ.md)
- [Cubical pinch](cubical-pinch.md)
- [Cells of CP^2](../chain-models/grid/cp2/cp2-cells.md)
- [Sequence category](../categories/asymptotic/point-sequence-category.md)
- [Point category](../categories/asymptotic/point-quotient.md)
- [The quotient functor of the point category](../categories/asymptotic/point-quotient-functor.md)
- [Induced map on ultimate L](../l-theory/ultimate/groups/induced-map.md)
- [The class map](../l-theory/ultimate/groups/ultimate-cls.md)
- [Embedding into the idempotent completion](../l-theory/base/categories/karoubi-embedding.md)
## Proof depends on
- [Labelled model](labelled-model.md)
- [Pinch faces](pinch-faces.md)
- [Inner cut formula](inner-cut-formula.md)
- [Box restriction](box-restriction.md)
- [Face restriction](face-restriction.md)
- [Pinch labels](pinch-labels.md)
- [Block pairs in the asymptotic category](../chain-models/blocks/block-pair-asymptotic.md)
- [Arc pair](../chain-models/blocks/arc-pair.md)
- [Excision equivalence](../categories/supports/excision.md)
- [Quotient by the empty support](../categories/supports/quotient-by-empty.md)
- [Scalar component projection](scalar-component-projection.md)
- [Relabelling equivalence](../categories/functors/relabelling-equivalence.md)
- [Equivalence invariance on ultimate L](../l-theory/ultimate/groups/equivalence-invariance.md)
- [Forgetting labels](../categories/functors/forget-labels.md)
- [Homotopy-isometry invariance](../l-theory/base/groups/homotopy-isometry-invariance.md)
- [Support of the whole space](../categories/supports/support-whole.md)
- [Exterior quotient](../categories/supports/exterior-quotient.md)
- [Functoriality on ultimate L](../l-theory/ultimate/groups/induced-map-comp.md)
