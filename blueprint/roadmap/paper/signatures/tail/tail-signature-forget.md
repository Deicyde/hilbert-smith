---
article_id: af_2c2b64ab64005ab27e50368e
declaration: lemma
origin: bridged
---

# Forgetting keeps the tail

For a group sequence $\mathbf G$ and $x\in\mathbb L_4(\mathcal V_{\mathbf G})$, $\sigma_{\mathrm{tail}}(\bar U_*x)=\sigma_{\mathrm{tail}}(x)$, where $\bar U:\mathcal V_{\mathbf G}\to\mathcal V_{\mathbf 1}$ is [the forgetful functor on tails](../point-functors/tail-forget-functor.md) and the left side is the tail signature of the trivial sequence.

This rests on the open statement [Lemma U](../../l-theory/comparison/lemma-u.md), through the [tail signature](tail-signature.md).

*Proof sketch.* Lift $x=q_*y$ ([tail-lift](tail-lift.md)). Since $\bar Uq=qU$, [functoriality](../../l-theory/ultimate/groups/induced-map-comp.md) gives $\bar U_*x=q_*U_*y$, and $\pi_iU=U_{G_i}\pi_i$ gives $(\pi_i)_*U_*y=(U_{G_i})_*(\pi_i)_*y$. Since [cls is natural](../../l-theory/ultimate/groups/induced-map-cls.md), $\mathrm{cls}^{-1}(U_{G_i})_*(\pi_i)_*y=(U_{G_i})_*\mathrm{cls}^{-1}(\pi_i)_*y$. Conclude coordinatewise with [forgetting keeps the integer signature](../l-four/signature-forget.md), and on both sides with [tail-signature-lift](tail-signature-lift.md).

## Sources

- HS paper, Section 3

## Depends on

- [Tail signature](tail-signature.md)
- [The forgetful functor on tails](../point-functors/tail-forget-functor.md)

## Proof depends on

- [Classes over $\mathcal V$ lift](tail-lift.md)
- [Functoriality on ultimate L](../../l-theory/ultimate/groups/induced-map-comp.md)
- [The induced map commutes with cls](../../l-theory/ultimate/groups/induced-map-cls.md)
- [Forgetting keeps the integer signature](../l-four/signature-forget.md)
- [Computing the tail signature](tail-signature-lift.md)
