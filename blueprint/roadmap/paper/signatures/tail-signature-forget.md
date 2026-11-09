---
declaration: lemma
origin: bridged
---

# Forgetting keeps the tail

$\sigma_{\mathrm{tail}}(\bar U_*x)=\sigma_{\mathrm{tail}}(x)$ for $x\in\mathbb L_4(\mathcal V_{\mathbf G})$.

*Proof sketch.* Lift $x$ to $y$ ([tail-lift](tail-lift.md)). Since $\bar Uq=qU$, functoriality gives $\bar U_*q_*y=q_*U_*y$, and $\pi_iU=U_{G_i}\pi_i$ gives $(\pi_i)_*U_*y=(U_{G_i})_*(\pi_i)_*y$. cls is natural. Conclude with [signature-forget](signature-forget.md) and [tail-signature-lift](tail-signature-lift.md).

## Sources

- HS paper, Section 3

## Depends on

- [Tail signature](tail-signature.md)
- [The forgetful functor on tails](tail-forget-functor.md)

## Proof depends on

- [Induced map on 𝕃](../l-theory/ultimate/induced-map.md)
- [Forgetting keeps the integer signature](signature-forget.md)
- [Computing the tail signature](tail-signature-lift.md)
