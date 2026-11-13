---
article_id: af_f97d77644e7ff6dc40477ba5
declaration: theorem
origin: bridged
statement: formalized
lean: HSP.Evaluation.tailSign_const
---
# Constant tail

Let $\mathbf P\in\mathcal P_{\mathbf 1}$ be the [constant sequence](constant-cp2-sequence.md) $(P,\varphi_P)$ in the [sequence category](../categories/asymptotic/point-sequence-category.md) of the trivial group sequence, and $q$ the quotient functor to the [point category](../categories/asymptotic/point-quotient.md). Then $\sigma_{\rm tail}(q_*\mathrm{cls}[\mathbf P])=[(1,1,\dots)]$, where $\mathrm{cls}[\mathbf P]$ is $\mathrm{cls}$ of the image of $\mathbf P$ under the [Karoubi embedding](../l-theory/base/categories/karoubi-embedding.md) $M\mapsto(M,1)$.

This rests on the open statements [Lemma U](../l-theory/comparison/lemma-u.md) and [lifting](../l-theory/localization/boundary/lift-to-pair.md), through the tail signature.

*Proof sketch.* By [computing the tail signature](../signatures/tail/tail-signature-lift.md), the $i$-th entry is $\sigma_{\{1\}}(\mathrm{cls}^{-1}(\pi_i)_*\mathrm{cls}[\mathbf P])$. By [the induced map commutes with cls](../l-theory/ultimate/groups/induced-map-cls.md), $(\pi_i)_*\mathrm{cls}[\mathbf P]=\mathrm{cls}[P,\varphi_P]$, and $\mathrm{cls}^{-1}$ of it is $[P,\varphi_P]$ by the [point comparison](../l-theory/comparison/free-comparison.md). Its signature is $1$ by the [signature of CP^2](cp2-signature.md).

## Sources
- HS paper, Section 12 (the tail of the constant sequence).
## Depends on

- [The constant sequence of CP^2](constant-cp2-sequence.md)
- [Tail signature](../signatures/tail/tail-signature.md)
- [Sequence category](../categories/asymptotic/point-sequence-category.md)
- [Point category](../categories/asymptotic/point-quotient.md)
- [Karoubi embedding](../l-theory/base/categories/karoubi-embedding.md)
- [Finite-support subcategory](../categories/asymptotic/eventually-zero-subcategory.md)
- [Point filtration](../categories/asymptotic/point-filtration.md)
- [The quotient functor of the point category](../categories/asymptotic/point-quotient-functor.md)
- [The trivial group sequence](../categories/asymptotic/trivial-group-sequence.md)
- [Quotient by a subcategory](../l-theory/base/categories/filtration-quotient.md)
- [Idempotent completion with duality](../l-theory/base/categories/karoubi-duality.md)
- [Group structure on L](../l-theory/base/groups/l-group-add.md)
- [L-group](../l-theory/base/groups/l-group.md)
- [The projective L-group](../l-theory/base/groups/projective-l-group.md)
- [Duality functors carry Poincaré complexes](../l-theory/base/pairs/functor-poincare.md)
- [Induced map on ultimate L](../l-theory/ultimate/groups/induced-map.md)
- [The class map](../l-theory/ultimate/groups/ultimate-cls.md)
- [Ultimate L-group](../l-theory/ultimate/groups/ultimate-l-group.md)

## Proof depends on

- [Computing the tail signature](../signatures/tail/tail-signature-lift.md)
- [The induced map commutes with cls](../l-theory/ultimate/groups/induced-map-cls.md)
- [Point comparison](../l-theory/comparison/free-comparison.md)
- [Signature of CP^2](cp2-signature.md)
- [Cells of CP^2](../chain-models/grid/cp2/cp2-cells.md)
