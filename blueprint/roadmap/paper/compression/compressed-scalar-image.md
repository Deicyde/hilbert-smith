---
article_id: af_f46364afa7ebaff76fe4e9a8
declaration: lemma
origin: bridged
statement: formalized
lean: HSP.Compression.scalar_image
---
# Scalar image of the compressed complex

Let $Z_0$ be the [exterior](../corner/exterior.md) for $n$ and the buffer radius $R$, $Z=T\times Z_0$, and $U':\mathcal B_{\mathbf 1,Z}(T\times S^n)\to\mathcal B_{\mathbf 1,Z_0}(S^n)$ [forgetting to the scalar exterior quotient](../corner/theorem/scalar-forget.md) for the trivial group sequence. Let $\mathfrak m_{f_T}$ be the [germ](../evaluation/germ.md) of the [torus test map](../chain-models/approximations/torus-test-map.md) $f_T$. Then
$$U'_*\operatorname{cls}(C,\hat\varphi)=\mathfrak m_{f_T}\quad\text{in }\mathbb L_N(\mathcal B_{\mathbf 1,Z_0}(S^n)),$$
with $(C,\hat\varphi)$, the [compressed Poincaré complex](compressed-poincare.md) with maps [represented](compressed-rep.md) by $\hat d$ and $\hat\varphi$, read in the idempotent completion through the [Karoubi embedding](../l-theory/base/categories/karoubi-embedding.md); here $\operatorname{cls}$ is the [class map](../l-theory/ultimate/groups/ultimate-cls.md) into the [ultimate L-group](../l-theory/ultimate/groups/ultimate-l-group.md) and $U'_*$ the [induced map](../l-theory/ultimate/groups/induced-map.md).

*Proof sketch.*
1. $U'_*\operatorname{cls}(C,\hat\varphi)=\operatorname{cls}(U'C,\hat\varphi)$ and $\mathfrak m_{f_T}=\operatorname{cls}(qD,\varphi)$, with $q$ the quotient functor and $D$ labelled by the sphere labels $s_b=f_T(x_b)$ ([the induced map commutes with cls](../l-theory/ultimate/groups/induced-map-cls.md); $U'$ is [strict](../corner/theorem/scalar-forget-strict.md)). $U'C$ has the labels $s_b$ of the retained cells.
2. Let $D'$ equal $D_i$ for $i\ge i_0$ and the zero module before. The identity for $i\ge i_0$ is a unitary isomorphism $D\cong D'$ in $\mathcal A_{\mathbf 1}(S^n)$, because morphisms are taken modulo eventual equality ([asymptotic category](../categories/asymptotic/asymptotic-category.md)).
3. In sphere labels, the [retained projection](retained-projection.md) $\mathrm{pr}:D'\to U'C$ and the [retained inclusion](retained-inclusion.md) $\mathrm{in}$ have propagation $0$. $\mathrm{pr}\,\mathrm{in}=1$, and $\mathrm{in}\,\mathrm{pr}=1-Q$, where the [projection onto the discarded cells](discard-projection.md) $Q$ factors with propagation $0$ through the span of the discarded cells, whose labels have $|s_b|>t>R$ or $s_b=\infty$ (as in the [endpoint lemma](endpoint-lemma.md) (3)); so $Q=0$ in $\mathcal B_{\mathbf 1,Z_0}(S^n)$ ([support ideal](../categories/supports/support-ideal.md)). Hence $\mathrm{pr}$ is a unitary isomorphism there, and it is a chain map ([compressed differential](compressed-differential.md)) with $\mathrm{pr}\,\varphi\,\mathrm{pr}^*=\hat\varphi$.
4. [Homotopy-isometry invariance](../l-theory/base/groups/homotopy-isometry-invariance.md) in $\operatorname{Kar}\mathcal B_{\mathbf 1,Z_0}(S^n)$, with the equivalence $\mathrm{pr}$ composed with $D\cong D'$ and $\chi=0$, gives $[qD,\varphi]=[U'C,\hat\varphi]$ in $L^p_N(\mathcal B_{\mathbf 1,Z_0}(S^n))=L_N(\operatorname{Kar}\mathcal B_{\mathbf 1,Z_0}(S^n))$ ([L-group](../l-theory/base/groups/l-group.md)); apply $\operatorname{cls}$ ([ultimate L-group](../l-theory/ultimate/groups/ultimate-l-group.md)).

## Sources
- HS paper, Section 10 (the scalar class after forgetting $T$).

## Depends on

- [Fixed local data](../local-data/control/fixed-local-data.md)
- [The control space](../local-data/control/control-space.md)
- [Strict symmetric Poincaré complex](../l-theory/base/pairs/symmetric-poincare-complex.md)
- [Exterior quotient](../categories/supports/exterior-quotient.md)
- [The trivial group sequence](../categories/asymptotic/trivial-group-sequence.md)
- [The round sphere](../corner/round-sphere.md)
- [Exterior](../corner/exterior.md)
- [Quotient by a subcategory](../l-theory/base/categories/filtration-quotient.md)
- [Compressed complex](compressed-complex.md)
- [Compressed maps](compressed-maps.md)
- [Chain model](../chain-models/grid/model/chain-model.md)
- [The category of based ℚ-vector spaces](../l-theory/localization/products/bookkeeping/based-category.md)
- [Forgetting to the scalar exterior quotient](../corner/theorem/scalar-forget.md)
- [Germ](../evaluation/germ.md)
- [The torus](../chain-models/grid/torus.md)
- [Torus test map](../chain-models/approximations/torus-test-map.md)
- [Embedding into the idempotent completion](../l-theory/base/categories/karoubi-embedding.md)
- [Duality functors carry Poincaré complexes](../l-theory/base/pairs/functor-poincare.md)
- [Morphisms represented by compressed matrices](compressed-rep.md)
- [L-group](../l-theory/base/groups/l-group.md)
- [Ultimate L-group and cls](../l-theory/ultimate/groups/ultimate-l-group.md)
- [The class map](../l-theory/ultimate/groups/ultimate-cls.md)
- [Induced map](../l-theory/ultimate/groups/induced-map.md)
- [Asymptotic category](../categories/asymptotic/asymptotic-category.md)
- [Duality on the asymptotic category](../categories/asymptotic/asymptotic-duality.md)
- [The asymptotic category has finite biproducts](../categories/asymptotic/structure/biproducts.md)
- [The support subcategory is additive](../categories/supports/support-dual-additive.md)
- [Support subcategory](../categories/supports/support-subcategory.md)
- [Idempotent completion with duality](../l-theory/base/categories/karoubi-duality.md)
- [Group structure on L](../l-theory/base/groups/l-group-add.md)
- [The projective L-group](../l-theory/base/groups/projective-l-group.md)
- [The cyclic action on the control space](../local-data/control/control-action.md)
- [The metric on the control space](../local-data/control/control-metric-space.md)
- [The control space is compact](../local-data/control/control-space-compact.md)

## Proof depends on

- [The compressed complex is Poincaré](compressed-poincare.md)
- [Retained projection](retained-projection.md)
- [Retained inclusion](retained-inclusion.md)
- [Projection onto the discarded cells](discard-projection.md)
- [Forgetting to the scalar exterior quotient is strict](../corner/theorem/scalar-forget-strict.md)
- [The induced map commutes with cls](../l-theory/ultimate/groups/induced-map-cls.md)
- [Homotopy-isometry invariance](../l-theory/base/groups/homotopy-isometry-invariance.md)
- [Support ideal](../categories/supports/support-ideal.md)
- [Compressed differential](compressed-differential.md)
- [Discarded subcomplex](discarded-subcomplex.md)
- [Endpoint lemma](endpoint-lemma.md)
- [Labelled chain model is Poincaré](../evaluation/labelled-model.md)
