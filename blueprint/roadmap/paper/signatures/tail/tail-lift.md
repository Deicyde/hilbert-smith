---
article_id: af_7cd202bfef2264af4166272c
declaration: theorem
origin: bridged
statement: formalized
lean: HSP.tail_lift
---

# Classes over $\mathcal V$ lift

Let $\mathbf G$ be a [group sequence](../../categories/asymptotic/group-sequence.md), $\mathcal P_{\mathbf G}$ its [sequence category](../../categories/asymptotic/point-sequence-category.md) and $q:\mathcal P_{\mathbf G}\to\mathcal V_{\mathbf G}$ the [quotient functor](../../categories/asymptotic/point-quotient-functor.md) onto its [point category](../../categories/asymptotic/point-quotient.md). Every $x\in\mathbb L_4(\mathcal V_{\mathbf G})$ is $q_*y$ for some $y\in\mathbb L_4(\mathcal P_{\mathbf G})$.

This rests on the open statements [Lemma U](../../l-theory/comparison/lemma-u.md), through [coordinates detect $\mathbb L_3(\mathcal S)$](../../l-theory/comparison/coordinates-injective-three.md), and [lifting](../../l-theory/localization/boundary/lift-to-pair.md), through the [ultimate boundary](../../l-theory/ultimate/boundary/ultimate-boundary.md) of the point filtration.

*Proof sketch.* The finite-support subcategory $\mathcal S_{\mathbf G}$ with the [point filtration](../../categories/asymptotic/point-filtration.md) is an involution-invariant Karoubi filtration of $\mathcal P_{\mathbf G}$, with inclusion $i$. $i_*\partial x=0$ in $\mathbb L_3(\mathcal P_{\mathbf G})$ by [the vanishing of boundary then inclusion](../../l-theory/ultimate/boundary/composite-zero.md). The coordinate functor $\pi_i$ of $\mathcal P_{\mathbf G}$ composed with $i$ is the coordinate functor of $\mathcal S_{\mathbf G}$, so [functoriality](../../l-theory/ultimate/groups/induced-map-comp.md) gives $(\pi_i)_*\partial x=(\pi_i)_*i_*\partial x=0$ for every $i$, and [coordinates detect $\mathbb L_3(\mathcal S)$](../../l-theory/comparison/coordinates-injective-three.md) gives $\partial x=0$. [Exactness at the quotient](../../l-theory/ultimate/boundary/exact-at-quotient.md) then provides $y$.

## Sources

- HS paper, Section 3

## Depends on

- [Group sequence](../../categories/asymptotic/group-sequence.md)
- [Sequence category](../../categories/asymptotic/point-sequence-category.md)
- [Point category](../../categories/asymptotic/point-quotient.md)
- [Ultimate L-group](../../l-theory/ultimate/groups/ultimate-l-group.md)
- [Induced map on ultimate L](../../l-theory/ultimate/groups/induced-map.md)
- [The quotient functor of the point category](../../categories/asymptotic/point-quotient-functor.md)
- [Finite-support subcategory](../../categories/asymptotic/eventually-zero-subcategory.md)
- [Point filtration](../../categories/asymptotic/point-filtration.md)
- [Quotient by a subcategory](../../l-theory/base/categories/filtration-quotient.md)

## Proof depends on

- [Ultimate boundary](../../l-theory/ultimate/boundary/ultimate-boundary.md)
- [Boundary then inclusion vanishes](../../l-theory/ultimate/boundary/composite-zero.md)
- [Functoriality on ultimate L](../../l-theory/ultimate/groups/induced-map-comp.md)
- [Coordinates detect $\mathbb L_3(\mathcal S)$](../../l-theory/comparison/coordinates-injective-three.md)
- [Ultimate exactness at the quotient](../../l-theory/ultimate/boundary/exact-at-quotient.md)
