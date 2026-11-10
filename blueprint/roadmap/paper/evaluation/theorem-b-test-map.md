---
article_id: af_4e2f05506c091aca9b1e8bab
declaration: theorem
origin: bridged
---
# Theorem B for the test map

Take [fixed local data](../local-data/control/fixed-local-data.md) with $D\le1/64$, with buffer radius $R$, and any $s$ with $0<s<R/\sqrt n$. Let $f_T$ be the [torus test map](../chain-models/approximations/torus-test-map.md), $\mathfrak m_{f_T}$ its [labelled-model class](germ.md) for $n$ and $R$, and $\Delta_{\mathbf 1}$ the [iterated cut](../corner/theorem/iterated-cut.md) for the cut sets of the [standing data](../corner/standing-data.md). Then
$$\sigma_{\rm tail}(\Delta_{\mathbf 1}\mathfrak m_{f_T})=[(\varepsilon,\varepsilon,\dots)]$$
with $\varepsilon\in\{\pm1\}$ the sign of [Theorem B](theorem-b.md).

This rests on the open statements [lifting](../l-theory/localization/boundary/lift-to-pair.md), through every cut boundary, and [Lemma U](../l-theory/comparison/lemma-u.md), through the tail signature.

*Proof sketch.* $f_T$ is homotopic to the cubical pinch $\kappa$ for $n$ and $s$ ([the torus test map is homotopic to the cubical pinch](test-map-to-pinch.md)). Apply [Theorem B](theorem-b.md) with $c=f_T$.

## Sources
- HS paper, Section 12.
## Depends on
- [Theorem B](theorem-b.md), [fixed local data](../local-data/control/fixed-local-data.md), [torus test map](../chain-models/approximations/torus-test-map.md), [labelled-model class](germ.md), [iterated cut](../corner/theorem/iterated-cut.md), [standing data](../corner/standing-data.md)
## Proof depends on
- [The torus test map is homotopic to the cubical pinch](test-map-to-pinch.md)
