---
article_id: af_0e4f3a5f3730269ed4641fee
declaration: theorem
origin: bridged
---

# Theorem A

Take the [standing data](../standing-data.md). Let $(C,\phi)$ be a strict $N$-dimensional symmetric Poincaré complex in $\mathcal B_{\mathbf 1,Z}(T\times S^n)$, concentrated in $[0,N]$, with a [graph-type homotopy action](../actions/graph-type-action.md) of $\mathbf G$. Let $U'$ be [forgetting to the scalar exterior quotient](scalar-forget.md) and $\Delta_{\mathbf 1}$ the [scalar iterated cut](scalar-iterated-cut.md) for the $n$, $R$, $s$ of the standing data. Then every representative $(\sigma_i)$ of
$$\sigma_{\mathrm{tail}}\big(\Delta_{\mathbf 1}U'_*\operatorname{cls}(C,\phi)\big)\in\mathbb Z^{\mathbb N}/\mathbb Z^{(\mathbb N)}$$
satisfies $p\mid\sigma_i$ for all sufficiently large $i$. Here $\operatorname{cls}(C,\phi)$ is $\operatorname{cls}$ of the complex read in $\operatorname{Kar}\mathcal B_{\mathbf 1,Z}(T\times S^n)$ through the [Karoubi embedding](../../l-theory/base/categories/karoubi-embedding.md), $(C,\phi)\mapsto((C,1),\phi)$.

This theorem rests on the open statements [Idempotents split in the bounded homotopy category](kb-idempotent-splitting.md) ([Balmer and Schlichting 2001, Theorem 2.8](../../../../sources/paper/balmer-schlichting-2001.md) [U]), through the corner class; [Lemma U](../../l-theory/comparison/lemma-u.md), through divisibility and the tail signature; and [Lifting](../../l-theory/localization/boundary/lift-to-pair.md), through the cut boundaries of the iterated cuts and through divisibility.

*Proof sketch.*
1. Form [the corner class](corner-class.md) $\mathfrak d\in\mathbb L_N(\mathcal B_{\mathbf G,Z}(T\times S^n))$.
2. Let $\Phi:\mathcal A_{\mathbf G}(T)\to\mathcal V_{\mathbf G}$ be [forgetting labels](../../categories/functors/forget-labels.md) (in this article $\Phi$ means only this functor). Every representative of $\sigma_{\mathrm{tail}}(\Phi_*\Delta_T\mathfrak d)$ is eventually divisible by $p$ ([Divisibility of the signature tail](../../divisibility/divisibility.md) for $X=T$, the group sequence $\mathbf G$ and $\alpha=\Delta_T\mathfrak d$; each $G_i$ is a finite $p$-group with $\chi_i$ onto, and $T$ is compact metric with a free isometric $C_p$-action).
3. Let $\bar U:\mathcal V_{\mathbf G}\to\mathcal V_{\mathbf 1}$ be [the forgetful functor on tails](../../signatures/point-functors/tail-forget-functor.md) and $U_T=\bar U\circ\Phi$. Then $\sigma_{\mathrm{tail}}(U_{T*}\Delta_T\mathfrak d)=\sigma_{\mathrm{tail}}(\bar U_*\Phi_*\Delta_T\mathfrak d)=\sigma_{\mathrm{tail}}(\Phi_*\Delta_T\mathfrak d)$ ([Functoriality](../../l-theory/ultimate/groups/induced-map-comp.md), [Forgetting keeps the tail](../../signatures/tail/tail-signature-forget.md)).
4. $U_{T*}\Delta_T\mathfrak d=\Delta_{\mathbf 1}U_*\mathfrak d$ ([Cuts commute with forgetting](cuts-commute-forgetting.md)).
5. $U_*\mathfrak d=U'_*\operatorname{cls}(C,\phi)$, with $U$ [forgetting to the scalar exterior quotient](scalar-forget.md) for $\mathbf G$ ([Scalar image](scalar-image.md)).

**Remark (not formalized).** The hypotheses are what the compression chapter's [Theorem C](../../compression/theorem-c.md) supplies for a nonempty control space, and Theorem C identifies $U'_*\operatorname{cls}(C,\phi)$ with the [labelled-model class](../../evaluation/germ.md) $\mathfrak m_{f_T}$ of the torus test map, which Theorem B evaluates.

## Sources

- HS paper, Sections 4, 11 and 12.
- New: stated over an arbitrary nonempty compact free isometric $C_p$-space.

## Depends on

- [Standing data](../standing-data.md)
- [Graph-type homotopy action](../actions/graph-type-action.md)
- [Strict symmetric Poincaré complex](../../l-theory/base/pairs/symmetric-poincare-complex.md)
- [Forgetting to the scalar exterior quotient](scalar-forget.md)
- [Scalar iterated cut](scalar-iterated-cut.md)
- [The tail signature](../../signatures/tail/tail-signature.md)
- [Ultimate L-group and cls](../../l-theory/ultimate/groups/ultimate-l-group.md)
- [Embedding into the idempotent completion](../../l-theory/base/categories/karoubi-embedding.md)

## Proof depends on

- [The corner class](corner-class.md)
- [Divisibility of the signature tail](../../divisibility/divisibility.md)
- [Iterated cut](iterated-cut.md)
- [Forgetting labels](../../categories/functors/forget-labels.md)
- [The forgetful functor on tails](../../signatures/point-functors/tail-forget-functor.md)
- [Functoriality on ultimate L](../../l-theory/ultimate/groups/induced-map-comp.md)
- [Forgetting keeps the tail](../../signatures/tail/tail-signature-forget.md)
- [Cuts commute with forgetting](cuts-commute-forgetting.md)
- [Scalar image of the corner](scalar-image.md)
