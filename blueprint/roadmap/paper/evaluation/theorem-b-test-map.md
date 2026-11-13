---
article_id: af_4e2f05506c091aca9b1e8bab
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: HSP.Evaluation.theoremB_testMap
---
# Theorem B for the test map

Take [fixed local data](../local-data/control/fixed-local-data.md) at a prime $p$ with $n\ge1$, local datum $A$, pinch radius $\rho$ and buffer radius $R$, and any $s$ with $0<s<R/\sqrt n$. Let $f_T$ be the [torus test map](../chain-models/approximations/torus-test-map.md) of $A$ and $\rho$, which is continuous ([properties of completed maps](../chain-models/approximations/completed-maps-properties.md), item 4), $\mathfrak m_{f_T}$ its [labelled-model class](germ.md) for $A$ and $R$, and $\Delta_{\mathbf 1}$ the [scalar iterated cut](../corner/theorem/scalar-iterated-cut.md) for $p$, $n$, $R$ and $s$ (with $\mathbf 1$ the trivial group sequence with values in $\mathbb Z/p$). Then there is $\varepsilon\in\{\pm1\}$ with
$$\sigma_{\rm tail}(\Delta_{\mathbf 1}\mathfrak m_{f_T})=[(\varepsilon,\varepsilon,\dots)].$$

This rests on the open statements [lifting](../l-theory/localization/boundary/lift-to-pair.md), through every cut boundary and the tail signature; [the two sides of an excision boundary](../l-theory/ultimate/boundary/excision-boundary-swap.md), through the inner cuts (evaluation at the cubical pinch); and [Lemma U](../l-theory/comparison/lemma-u.md), through the tail signature. Its formal proof also reaches, through [Theorem B](theorem-b.md), the stated results with incomplete formal proofs listed there (these are not open statements).

*Proof sketch.* A continuous homotopy joins $f_T$ to the cubical pinch $\kappa$ for $n$ and $s$ ([the torus test map is homotopic to the cubical pinch](test-map-to-pinch.md)), so $f_T$ is continuous and homotopic to $\kappa$. Apply [Theorem B](theorem-b.md) with $c=f_T$.

## Sources
- HS paper, Section 12.
## Depends on

- [Fixed local data](../local-data/control/fixed-local-data.md)
- [Torus test map](../chain-models/approximations/torus-test-map.md)
- [Labelled-model class](germ.md)
- [Scalar iterated cut](../corner/theorem/scalar-iterated-cut.md)
- [Tail signature](../signatures/tail/tail-signature.md)
- [The trivial group sequence](../categories/asymptotic/trivial-group-sequence.md)
- [The torus](../chain-models/grid/torus.md)
- [The round sphere](../corner/round-sphere.md)
- [Asymptotic category](../categories/asymptotic/asymptotic-category.md)
- [Duality on the asymptotic category](../categories/asymptotic/asymptotic-duality.md)
- [Finite-support subcategory](../categories/asymptotic/eventually-zero-subcategory.md)
- [Point filtration](../categories/asymptotic/point-filtration.md)
- [Point category](../categories/asymptotic/point-quotient.md)
- [Sequence category](../categories/asymptotic/point-sequence-category.md)
- [The asymptotic category has finite biproducts](../categories/asymptotic/structure/biproducts.md)
- [Exterior quotient](../categories/supports/exterior-quotient.md)
- [The support subcategory is additive](../categories/supports/support-dual-additive.md)
- [Support subcategory](../categories/supports/support-subcategory.md)
- [The exterior](../corner/exterior.md)
- [Quotient by a subcategory](../l-theory/base/categories/filtration-quotient.md)
- [Ultimate L-group](../l-theory/ultimate/groups/ultimate-l-group.md)

## Proof depends on

- [The torus test map is homotopic to the cubical pinch](test-map-to-pinch.md)
- [Theorem B](theorem-b.md)
- [Cubical pinch](cubical-pinch.md)
- [Local datum](../local-data/chart/local-datum.md)
