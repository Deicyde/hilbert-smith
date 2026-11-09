---
declaration: def
origin: bridged
---

# The tail signature

$\sigma_{\mathrm{tail}}:\mathbb L_4(\mathcal V)\to\mathbb Z^{\mathbb N}/\mathbb Z^{(\mathbb N)}$ sends $x$ to the class of $\big(\sigma_{G_i}(\mathrm{cls}^{-1}(\pi_i)_*y)\big)_i$, for a chosen lift $y$. It is an additive homomorphism.

*Proof sketch.* $\mathrm{cls}^{-1}$ exists by [E5](../l-theory/E5.md). Lifts exist by [tail-lift](tail-lift.md). The class is independent of the lift by [eventual agreement](tail-lift-eventual.md). Since $y+y'$ lifts $x+x'$, the map is additive.

## Sources

- HS paper, Section 3

## Depends on

- [Integer signature](integer-signature.md)
- [E5](../l-theory/E5.md)

## Proof depends on

- [Lifts](tail-lift.md), [eventual agreement](tail-lift-eventual.md)
