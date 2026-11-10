---
article_id: af_0e4f3a5f3730269ed4641fee
declaration: theorem
origin: bridged
---

# Theorem A

Take the [standing data](../standing-data.md). Let $(C,\phi)$ be a strict $N$-dimensional symmetric Poincaré complex in $\mathcal B_{\mathbf 1,Z}(T\times S^n)$, concentrated in $[0,N]$, with a [graph-type homotopy action](../actions/graph-type-action.md) of $\mathbf G$. Let $U'$ be as in [Scalar image](scalar-image.md) and $\Delta_{\mathbf 1}$ the [iterated cut](iterated-cut.md). Then every representative $(\sigma_i)$ of
$$\sigma_{\mathrm{tail}}\big(\Delta_{\mathbf 1}U'_*\operatorname{cls}(C,\phi)\big)\in\mathbb Z^{\mathbb N}/\mathbb Z^{(\mathbb N)}$$
satisfies $p\mid\sigma_i$ for all sufficiently large $i$.

This theorem rests on the open statement [Idempotents split in the bounded homotopy category](kb-idempotent-splitting.md) ([Balmer and Schlichting 2001, Theorem 2.8](../../../../sources/paper/balmer-schlichting-2001.md) [U]), through the corner class.

*Proof sketch.*
1. Form [the corner class](corner-class.md) $\mathfrak d\in\mathbb L_N(\mathcal B_{\mathbf G,Z}(T\times S^n))$.
2. Every representative of $\sigma_{\mathrm{tail}}(\Phi_*\Delta_T\mathfrak d)$ is eventually divisible by $p$ ([Divisibility of the signature tail](../../divisibility/divisibility.md) for $X=T$ and $\alpha=\Delta_T\mathfrak d$).
3. $\sigma_{\mathrm{tail}}(U_{T*}\Delta_T\mathfrak d)=\sigma_{\mathrm{tail}}(\bar U_*\Phi_*\Delta_T\mathfrak d)=\sigma_{\mathrm{tail}}(\Phi_*\Delta_T\mathfrak d)$, with $U_T=\bar U\circ\Phi$ ([Functoriality](../../l-theory/ultimate/groups/induced-map-comp.md), [Forgetting keeps the tail](../../signatures/tail/tail-signature-forget.md)).
4. $U_{T*}\Delta_T\mathfrak d=\Delta_{\mathbf 1}U_*\mathfrak d$ ([Cuts commute with forgetting](cuts-commute-forgetting.md)).
5. $U_*\mathfrak d=U'_*\operatorname{cls}(C,\phi)$ ([Scalar image](scalar-image.md)).

**Remark (not formalized).** The hypotheses are what the compression chapter's [Theorem C](../../compression/theorem-c.md) supplies for the control space, and Theorem C identifies $U'_*\operatorname{cls}(C,\phi)$ with the labelled-model class of the torus test map, which Theorem B evaluates.

## Sources

- HS paper, Sections 4, 11 and 12.
- New: stated over an arbitrary nonempty compact free isometric $C_p$-space.

## Depends on

- [Standing data](../standing-data.md)
- [Graph-type homotopy action](../actions/graph-type-action.md)
- [Strict symmetric Poincaré complex](../../l-theory/base/pairs/symmetric-poincare-complex.md)
- [Scalar image of the corner](scalar-image.md)
- [Iterated cut](iterated-cut.md)
- [The tail signature](../../signatures/tail/tail-signature.md)
- [Ultimate L-group and cls](../../l-theory/ultimate/groups/ultimate-l-group.md)

## Proof depends on

- [The corner class](corner-class.md)
- [Divisibility of the signature tail](../../divisibility/divisibility.md)
- [Functoriality on ultimate L](../../l-theory/ultimate/groups/induced-map-comp.md)
- [Forgetting keeps the tail](../../signatures/tail/tail-signature-forget.md)
- [Cuts commute with forgetting](cuts-commute-forgetting.md)
- [Scalar image of the corner](scalar-image.md)
