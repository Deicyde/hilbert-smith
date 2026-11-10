---
article_id: af_ec9960b49e65ad6dc27b13e4
declaration: theorem
origin: bridged
---
# Theorem B

Let $n\ge1$, $R>0$ and $0<s<R/\sqrt n$. Let $\kappa:\mathbb T^n\to S^n$ be the [cubical pinch](cubical-pinch.md) for $n$ and $s$, $\mathfrak m$ the [labelled-model class](germ.md) for $n$ and $R$, and $\Delta_{\mathbf 1}$ the [iterated cut](../corner/theorem/iterated-cut.md) for the cut sets of the [standing data](../corner/standing-data.md). There is $\varepsilon\in\{\pm1\}$, depending only on $n$, such that for every continuous $c:\mathbb T^n\to S^n$ homotopic to $\kappa$,
$$\sigma_{\rm tail}(\Delta_{\mathbf 1}\mathfrak m_c)=[(\varepsilon,\varepsilon,\dots)]\in\mathbb Z^{\mathbb N}/\mathbb Z^{(\mathbb N)}.$$

This rests on the open statements [lifting](../l-theory/localization/boundary/lift-to-pair.md), through every cut boundary, and [Lemma U](../l-theory/comparison/lemma-u.md), through the tail signature.

*Proof sketch.* $\mathfrak m_c=\mathfrak m_\kappa$ ([homotopic labellings have equal classes](germ-homotopy.md)). By [evaluation at the cubical pinch](pinch-evaluation.md), $\Delta_{\mathbf 1}\mathfrak m_\kappa=\varepsilon\,q_*\mathrm{cls}[\mathbf P]$ with $\varepsilon=(-1)^{n(n+1)/2}$. The [tail signature](../signatures/tail/tail-signature.md) is additive, and the [constant tail](constant-tail.md) is $[(1,1,\dots)]$.

## Sources
- HS paper, Section 12 (Proposition 12.4).
- New: the hypothesis is a homotopy to the cubical pinch, with no degree theory.
## Depends on
- [Iterated cut](../corner/theorem/iterated-cut.md), [standing data](../corner/standing-data.md), [labelled-model class](germ.md), [cubical pinch](cubical-pinch.md), [tail signature](../signatures/tail/tail-signature.md)
## Proof depends on
- [Homotopic labellings have equal classes](germ-homotopy.md), [evaluation at the cubical pinch](pinch-evaluation.md), [constant tail](constant-tail.md)
