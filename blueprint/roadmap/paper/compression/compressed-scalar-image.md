---
article_id: af_f46364afa7ebaff76fe4e9a8
declaration: lemma
origin: bridged
---
# Scalar image of the compressed complex

Let $U':\mathcal B_{\mathbf 1,Z}(T\times S^n)\to\mathcal B_{\mathbf 1,Z_0}(S^n)$ be the functor of [scalar image of the corner](../corner/theorem/scalar-image.md): the functor on [exterior quotients](../categories/supports/exterior-functor.md) induced by [forgetting the control space](../categories/functors/forget-control.md) for the trivial group sequence. Let $\mathfrak m_{f_T}$ be the [germ](../evaluation/germ.md) of the [torus test map](../chain-models/approximations/torus-test-map.md) $f_T$. Then
$$U'_*\operatorname{cls}(C,\hat\varphi)=\mathfrak m_{f_T}\quad\text{in }\mathbb L_N(\mathcal B_{\mathbf 1,Z_0}(S^n)).$$

*Proof sketch.*
1. $U'_*\operatorname{cls}(C,\hat\varphi)=\operatorname{cls}(U'C,\hat\varphi)$ and $\mathfrak m_{f_T}=\operatorname{cls}(qD,\varphi)$, with $q$ the quotient functor and $D$ labelled by the sphere labels $s_b=f_T(x_b)$ ([the induced map commutes with cls](../l-theory/ultimate/groups/induced-map-cls.md); $U'$ is strict). $U'C$ has the labels $s_b$ of the retained cells.
2. Let $D'$ equal $D_i$ for $i\ge i_0$ and the zero module before. The identity for $i\ge i_0$ is a unitary isomorphism $D\cong D'$ in $\mathcal A_{\mathbf 1}(S^n)$, because morphisms are taken modulo eventual equality ([asymptotic category](../categories/asymptotic/asymptotic-category.md)).
3. In sphere labels, $\mathrm{pr}:D'\to U'C$ and $\mathrm{in}$ have propagation $0$. $\mathrm{pr}\,\mathrm{in}=1$, and $\mathrm{in}\,\mathrm{pr}=1-Q$, where $Q$ factors with propagation $0$ through the span of the discarded cells, whose labels have $|s_b|>t>R$ or $s_b=\infty$ (as in the [endpoint lemma](endpoint-lemma.md) (3)); so $Q=0$ in $\mathcal B_{\mathbf 1,Z_0}(S^n)$ ([support ideal](../categories/supports/support-ideal.md)). Hence $\mathrm{pr}$ is a unitary isomorphism there, and it is a chain map ([compressed differential](compressed-differential.md)) with $\mathrm{pr}\,\varphi\,\mathrm{pr}^*=\hat\varphi$.
4. [Homotopy-isometry invariance](../l-theory/base/groups/homotopy-isometry-invariance.md) in $\operatorname{Kar}\mathcal B_{\mathbf 1,Z_0}(S^n)$, with the equivalence $\mathrm{pr}$ composed with $D\cong D'$ and $\chi=0$, gives $[qD,\varphi]=[U'C,\hat\varphi]$ in $L^p_N$; apply $\operatorname{cls}$.

## Sources
- HS paper, Section 10 (the scalar class after forgetting $T$).
## Depends on
- [Compressed Poincaré](compressed-poincare.md), [scalar image of the corner](../corner/theorem/scalar-image.md), [forgetting the control space](../categories/functors/forget-control.md), [forgetting the control space preserves support](../categories/functors/forget-control-support.md), [induced functor on exterior quotients](../categories/supports/exterior-functor.md), [germ](../evaluation/germ.md), [torus test map](../chain-models/approximations/torus-test-map.md)
## Proof depends on
- [The induced map commutes with cls](../l-theory/ultimate/groups/induced-map-cls.md), [homotopy-isometry invariance](../l-theory/base/groups/homotopy-isometry-invariance.md), [asymptotic category](../categories/asymptotic/asymptotic-category.md), [support ideal](../categories/supports/support-ideal.md), [compressed differential](compressed-differential.md), [discarded subcomplex](discarded-subcomplex.md), [endpoint lemma](endpoint-lemma.md), [labelled chain model is Poincaré](../evaluation/labelled-model.md)
