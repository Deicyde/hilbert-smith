---
article_id: af_3d0138ecba1b8c5c117da4ba
declaration: def
origin: bridged
statement: formalized
lean: HSP.tailSign
---

# The tail signature

Let $\mathbf G$ be a [group sequence](../../categories/asymptotic/group-sequence.md). $\sigma_{\mathrm{tail}}:\mathbb L_4(\mathcal V_{\mathbf G})\to\mathbb Z^{\mathbb N}/\mathbb Z^{(\mathbb N)}$ sends $x$ to the class of $\big(\sigma_{G_i}(\mathrm{cls}^{-1}(\pi_i)_*y)\big)_i$, for a chosen $y\in\mathbb L_4(\mathcal P_{\mathbf G})$ with $q_*y=x$, $q$ the [quotient functor](../../categories/asymptotic/point-quotient-functor.md). Here $\mathcal V_{\mathbf G}$ is the [point category](../../categories/asymptotic/point-quotient.md), $\pi_i$ are the [coordinate functors](../../categories/asymptotic/point-coordinate-projection.md) of the [sequence category](../../categories/asymptotic/point-sequence-category.md), $\mathrm{cls}:L^p_4(\mathrm{Free}(\mathbb Q[G_i]))\to\mathbb L_4(\mathrm{Free}(\mathbb Q[G_i]))$ is the bijection of the [point comparison](../../l-theory/comparison/free-comparison.md), and $\sigma_{G_i}$ is the [integer signature](../l-four/integer-signature.md). The definition is an additive homomorphism; its two proof obligations, that the class does not depend on the lift $y$ and that the map is additive, are discharged in the proof sketch, and the definition asserts nothing else.

This rests on the open statements [Lemma U](../../l-theory/comparison/lemma-u.md), through the point comparison and the coordinate lemmas of the L-theory comparison, and [lifting](../../l-theory/localization/boundary/lift-to-pair.md), through the localization boundary of the [point filtration](../../categories/asymptotic/point-filtration.md), which [classes over $\mathcal V$ lift](tail-lift.md) and [lifts agree eventually](tail-lift-eventual.md) use.

*Proof sketch.* $\mathrm{cls}^{-1}$ exists by the [point comparison](../../l-theory/comparison/free-comparison.md). Lifts exist by [tail-lift](tail-lift.md). The class is independent of the lift by [eventual agreement](tail-lift-eventual.md). Since $y+y'$ lifts $x+x'$ and $(\pi_i)_*$, $\mathrm{cls}^{-1}$ and $\sigma_{G_i}$ are additive, the map is additive.

## Sources

- HS paper, Section 3

## Depends on

- [Group sequence](../../categories/asymptotic/group-sequence.md)
- [Point category](../../categories/asymptotic/point-quotient.md)
- [Sequence category](../../categories/asymptotic/point-sequence-category.md)
- [Integer signature](../l-four/integer-signature.md)
- [Point comparison for the free categories](../../l-theory/comparison/free-comparison.md)
- [Coordinate projection of the sequence category](../../categories/asymptotic/point-coordinate-projection.md)
- [The quotient functor of the point category](../../categories/asymptotic/point-quotient-functor.md)

## Proof depends on

- [Classes over $\mathcal V$ lift](tail-lift.md)
- [Lifts agree eventually](tail-lift-eventual.md)
