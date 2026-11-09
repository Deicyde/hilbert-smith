---
article_id: af_3d0138ecba1b8c5c117da4ba
declaration: def
origin: bridged
---

# The tail signature

$\sigma_{\mathrm{tail}}:\mathbb L_4(\mathcal V)\to\mathbb Z^{\mathbb N}/\mathbb Z^{(\mathbb N)}$ sends $x$ to the class of $\big(\sigma_{G_i}(\mathrm{cls}^{-1}(\pi_i)_*y)\big)_i$, for a chosen lift $y$. It is an additive homomorphism.

*Proof sketch.* $\mathrm{cls}^{-1}$ exists by the [point comparison](../../l-theory/comparison/free-comparison.md). Lifts exist by [tail-lift](tail-lift.md). The class is independent of the lift by [eventual agreement](tail-lift-eventual.md). Since $y+y'$ lifts $x+x'$, the map is additive.

## Sources

- HS paper, Section 3

## Depends on

- [Integer signature](../l-four/integer-signature.md)
- [Point comparison for a group ring](../../l-theory/comparison/free-comparison.md)

## Proof depends on

- [Lifts](tail-lift.md), [eventual agreement](tail-lift-eventual.md)
