---
article_id: af_2d547e7264821dc49722c203
declaration: lemma
origin: bridged
statement: formalized
lean: HSP.Compression.compressed_poincare
---
# The compressed complex is Poincaré

Let $Z_0$ be the [exterior](../corner/exterior.md) for $n$ and the buffer radius $R$, and $Z=T\times Z_0$ for the control space $T$, possibly empty; $Z$ is closed and invariant ([the exterior is closed](../corner/exterior-closed.md)). Then $(C,\hat\varphi)$, with differential $\hat d$, is a [strict $N$-dimensional symmetric Poincaré complex](../l-theory/base/pairs/symmetric-poincare-complex.md) in the [exterior quotient](../categories/supports/exterior-quotient.md) $\mathcal B_{\mathbf 1,Z}(T\times S^n)$, concentrated in $[0,N]$, whose chain objects are the compressed objects in $\mathcal B_{\mathbf 1,Z}(T\times S^n)$, and whose maps are the images of the morphisms [represented](compressed-rep.md) by $\hat d$ and $\hat\varphi$. A homotopy inverse of $\hat\varphi_\natural$ is $\hat b$, with homotopies $\hat H$ and $\hat H'$.

*Proof sketch.*
1. Morphisms. $\hat d$ has propagation at most $\delta_i$, the [bound sequence](bound-sequence.md) ([compressed differential](compressed-differential.md)). For $i\ge i_0$, $\hat\varphi,\hat b,\hat H,\hat H'$ are submatrices of $w^{[u]}$ for type-$0$ elements $w\in\mathcal P_i$, because retained cells lie in $\mathcal B_i(u)$ ([buffer condition](buffer-conditions.md) (1), which holds from the [start index](start-index.md) on). By buffer condition (3) these submatrices have graph type $0$ with bound $\delta_i$. Since $0\cdot\lambda=\lambda$, the labels of every nonzero entry are within $\delta_i$ of each other, so the propagation is at most $\delta_i$. Since $\delta_i\to0$ ([the bound sequence is null](bound-sequence-null.md)), all of them are morphisms of $\mathcal A_{\mathbf 1}(T\times S^n)$.
2. [Residuals](compressed-residuals.md) (4) give $\partial\hat\varphi=0$ and invariance under the involution, exactly.
3. In residuals (5)-(7), every word on the right is $p_2\alpha Q_1\beta\jmath_0$ with $\alpha,\beta$ of type $0$. By the [endpoint lemma](endpoint-lemma.md) it is $x\,y$ through $W_i$, with $x,y$ of propagation at most $\delta_i$ and every label of $W_i$ in $Z$. So the levelwise sums factor through an object of $\mathcal A_Z$ ([sums of witnesses](../corner/actions/witness-sum.md)), and they are zero in $\mathcal B_{\mathbf 1,Z}(T\times S^n)$. Below $i_0$ all maps are zero, and morphisms are taken modulo eventual equality.
4. Dual differential. Residuals (5) and (7) are stated with $\hat d^\vee$, the compression of the differential of $D_i^{N-*}$, while the differential of $C^{N-*}$ in degree $r$ is $(-1)^r$ times the transpose of $\hat d_{N-r+1}$, the dual of a morphism of based objects being represented by its transpose. The two agree. The retained inclusion is $\mathrm{in}_i=\mathrm{pr}_i^T$, so on cochains the retained projection is $\mathrm{in}_i^*=\mathrm{pr}_i$ and the retained inclusion is $\mathrm{pr}_i^*=\mathrm{in}_i$. The differential of $D_i^{N-*}$ in degree $r$ is $(-1)^r d_{N-r+1}^T$, so $\hat d^\vee_r=(-1)^r\,\mathrm{pr}_i\,d_{N-r+1}^T\,\mathrm{in}_i=(-1)^r(\mathrm{pr}_i\,d_{N-r+1}\,\mathrm{in}_i)^T=(-1)^r(\hat d_{N-r+1})^T$. So (5) says that $\hat b$ commutes with the differentials of $C$ and $C^{N-*}$, and (7) is the homotopy identity for $\hat H'$ on $C^{N-*}$.
5. Hence $\hat b$ is a chain map, and $\hat\varphi_\natural\hat b\simeq1$, $\hat b\hat\varphi_\natural\simeq1$ through $\hat H,\hat H'$.

## Sources
- HS paper, Section 10 (compressed realization). New: symmetric over $\mathbb Q$, with no quadratic halving.

## Depends on

- [Compressed maps](compressed-maps.md)
- [Strict Poincaré complex](../l-theory/base/pairs/symmetric-poincare-complex.md)
- [Exterior quotient](../categories/supports/exterior-quotient.md)
- [Exterior](../corner/exterior.md)
- [Morphisms represented by compressed matrices](compressed-rep.md)
- [Asymptotic category](../categories/asymptotic/asymptotic-category.md)
- [Duality on the asymptotic category](../categories/asymptotic/asymptotic-duality.md)
- [The asymptotic category has finite biproducts](../categories/asymptotic/structure/biproducts.md)
- [The trivial group sequence](../categories/asymptotic/trivial-group-sequence.md)
- [The support subcategory is additive](../categories/supports/support-dual-additive.md)
- [Support subcategory](../categories/supports/support-subcategory.md)
- [Chain model](../chain-models/grid/model/chain-model.md)
- [Compressed complex](compressed-complex.md)
- [The round sphere](../corner/round-sphere.md)
- [Quotient by a subcategory](../l-theory/base/categories/filtration-quotient.md)
- [Duality map of a cycle](../l-theory/base/complexes/cycle-chain-map.md)
- [Dual complex](../l-theory/base/complexes/dual-complex.md)
- [The category of based ℚ-vector spaces](../l-theory/localization/products/bookkeeping/based-category.md)
- [The cyclic action on the control space](../local-data/control/control-action.md)
- [The metric on the control space](../local-data/control/control-metric-space.md)
- [The control space](../local-data/control/control-space.md)
- [Fixed local data](../local-data/control/fixed-local-data.md)

## Proof depends on

- [Bound sequence](bound-sequence.md)
- [The bound sequence is null](bound-sequence-null.md)
- [Residuals](compressed-residuals.md)
- [Endpoint lemma](endpoint-lemma.md)
- [Buffers hold eventually](buffer-eventually.md)
- [Sums of witnesses](../corner/actions/witness-sum.md)
- [Support ideal](../categories/supports/support-ideal.md)
- [Compressed differential](compressed-differential.md)
- [The exterior is closed](../corner/exterior-closed.md)
