---
article_id: af_0e4f3a5f3730269ed4641fee
declaration: theorem
origin: bridged
---

# Theorem A

Take the standing data, with $T$ any compact metric space with a free isometric $C_p$-action. Let $(C,\phi)$ be a strict $N$-dimensional symmetric Poincaré complex in $\mathcal B_{\mathbf 1,Z}(T\times S^n)$, concentrated in $[0,N]$, with a graph-type homotopy action of $\mathbf G$. Then

$$\sigma_{\mathrm{tail}}\big(\Delta_{\mathbf 1}U'_*\operatorname{cls}(C,\phi)\big)\in p\,\mathbb Z^{\mathbb N}/\mathbb Z^{(\mathbb N)}.$$

That is, the signatures of the iterated cut are eventually divisible by $p$.

*Proof sketch.*
1. Form the induced complex ([Induction](../actions/induction.md)) and the average ([Average is a compatible idempotent](../actions/average-compatible-idempotent.md)).
2. Split ([Splitting](homotopy-idempotent-splitting.md), [Corner duality](corner-duality.md)) to get $\mathfrak d$ ([The corner class](corner-class.md)).
3. $\sigma_{\mathrm{tail}}(\Delta_T\mathfrak d)$ is eventually divisible by $p$ ([Integer tail divisibility](../../divisibility/divisibility.md)).
4. $\sigma_{\mathrm{tail}}U_{T*}=\sigma_{\mathrm{tail}}$ ([Forgetting keeps signature](../../signatures/tail/tail-signature-forget.md)).
5. $U_{T*}\Delta_T\mathfrak d=\Delta_{\mathbf 1}U_*\mathfrak d$ ([Cuts commute with forgetting](cuts-commute-forgetting.md)).
6. $U_*\mathfrak d=U'_*\operatorname{cls}(C,\phi)$ ([Scalar image](scalar-image.md)).

## Sources

- HS paper, Sections 4, 11, 12.
- New: stated over an arbitrary compact free isometric $C_p$-space.

## Depends on

- [Graph-type homotopy action](../actions/graph-type-action.md)
- [Iterated cut](iterated-cut.md)
- [Signature tail](../../signatures/tail/tail-signature.md)

## Proof depends on

- [The corner class](corner-class.md)
- [Scalar image](scalar-image.md)
- [Cuts commute with forgetting](cuts-commute-forgetting.md)
- [Integer tail divisibility](../../divisibility/divisibility.md)
- [Forgetting keeps signature](../../signatures/tail/tail-signature-forget.md)
