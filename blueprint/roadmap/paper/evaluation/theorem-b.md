---
article_id: af_ec9960b49e65ad6dc27b13e4
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: HSP.Evaluation.theoremB
---
# Theorem B

Let $n\ge1$. There is $\varepsilon\in\{\pm1\}$ such that for every prime $p$, all reals $D,\rho_+,R,s$ with $R>0$ and $0<s<R/\sqrt n$, every [local datum](../local-data/chart/local-datum.md) $A$ at $p$ in dimension $n$ with constants $(D,\rho_+)$, and every continuous $c:\mathbb T^n\to S^n$ homotopic to the [cubical pinch](cubical-pinch.md) $\kappa$ for $n$ and $s$,
$$\sigma_{\rm tail}(\Delta_{\mathbf 1}\mathfrak m_c)=[(\varepsilon,\varepsilon,\dots)]\in\mathbb Z^{\mathbb N}/\mathbb Z^{(\mathbb N)},$$
where $\mathfrak m_c$ is the [labelled-model class](germ.md) of $c$ for $A$ and $R$, $\Delta_{\mathbf 1}$ is the [scalar iterated cut](../corner/theorem/scalar-iterated-cut.md) for $p$, $n$, $R$ and $s$ (with $\mathbf 1$ the trivial group sequence with values in $\mathbb Z/p$), and $\sigma_{\rm tail}$ is the [tail signature](../signatures/tail/tail-signature.md) of $\mathbf 1$. So $\varepsilon$ is chosen before $p$, $D$, $\rho_+$, $R$, $s$, $A$ and $c$, and depends only on $n$.

This rests on the open statements [lifting](../l-theory/localization/boundary/lift-to-pair.md), through every cut boundary and the tail signature; [the two sides of an excision boundary](../l-theory/ultimate/boundary/excision-boundary-swap.md), through the inner cuts (evaluation at the cubical pinch); and [Lemma U](../l-theory/comparison/lemma-u.md), through the tail signature. Its formal proof also reaches stated results whose formal proofs are not yet complete (these are not open statements): [Homotopic labellings have equal classes](germ-homotopy.md), [Evaluation at the cubical pinch](pinch-evaluation.md) and [Constant tail](constant-tail.md), used directly, and The labelled chain model is Poincaré, through the labelled-model class; Lifting closed complexes, Independence of the lift, Transition commutes with the boundary and Products with the line are decorated, through the cut boundaries; Point comparison for the free categories, Boundaries have zero signature, The middle form is nonsingular, symmetric and invariant, Middle form of a sum, Classes over $\mathcal V$ lift and Lifts agree eventually, through the tail signature; Naturality of the transition, through the induced maps on ultimate L; and Cobordism is an equivalence relation, through the L-groups.

*Proof sketch.* $\mathfrak m_c=\mathfrak m_\kappa$ ([homotopic labellings have equal classes](germ-homotopy.md)). By [evaluation at the cubical pinch](pinch-evaluation.md), $\Delta_{\mathbf 1}\mathfrak m_\kappa=\varepsilon\,q_*\mathrm{cls}[\mathbf P]$, for the [constant sequence](constant-cp2-sequence.md) $\mathbf P$, with $\varepsilon=(-1)^{n(n+1)/2}$. The [tail signature](../signatures/tail/tail-signature.md) is additive, so it commutes with multiplication by $\varepsilon$, and the [constant tail](constant-tail.md) is $[(1,1,\dots)]$; hence $\sigma_{\rm tail}(\Delta_{\mathbf 1}\mathfrak m_c)=\varepsilon[(1,1,\dots)]=[(\varepsilon,\varepsilon,\dots)]$, with $\varepsilon$ depending only on $n$.

## Sources
- HS paper, Section 12 (Proposition 12.4).
- New: the hypothesis is a homotopy to the cubical pinch, with no degree theory.
## Depends on

- [Scalar iterated cut](../corner/theorem/scalar-iterated-cut.md)
- [Labelled-model class](germ.md)
- [Local datum](../local-data/chart/local-datum.md)
- [Cubical pinch](cubical-pinch.md)
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

- [The constant sequence of CP^2](constant-cp2-sequence.md)
- [Homotopic labellings have equal classes](germ-homotopy.md)
- [Evaluation at the cubical pinch](pinch-evaluation.md)
- [Constant tail](constant-tail.md)
- [The quotient functor of the point category](../categories/asymptotic/point-quotient-functor.md)
- [Idempotent completion with duality](../l-theory/base/categories/karoubi-duality.md)
- [Embedding into the idempotent completion](../l-theory/base/categories/karoubi-embedding.md)
- [Group structure on L](../l-theory/base/groups/l-group-add.md)
- [L-group](../l-theory/base/groups/l-group.md)
- [The projective L-group](../l-theory/base/groups/projective-l-group.md)
- [Duality functors carry Poincaré complexes](../l-theory/base/pairs/functor-poincare.md)
- [Induced map on ultimate L](../l-theory/ultimate/groups/induced-map.md)
- [The class map](../l-theory/ultimate/groups/ultimate-cls.md)
