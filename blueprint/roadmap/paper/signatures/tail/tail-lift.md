---
article_id: af_7cd202bfef2264af4166272c
declaration: lemma
origin: bridged
---

# Classes over $\mathcal V$ lift

Every $x\in\mathbb L_4(\mathcal V)$ is $q_*y$ for some $y\in\mathbb L_4(\mathcal P)$.

*Proof sketch.* $i_*\partial x=0$ in $\mathbb L_3(\mathcal P)$ by [the vanishing of boundary then inclusion](../../l-theory/ultimate/boundary/composite-zero.md). Since $\pi_i\circ i$ is the coordinate functor of $\mathcal S$, injectivity of the [coordinates](../../l-theory/comparison/coordinates-injective-three.md) and [functoriality](../../l-theory/ultimate/groups/induced-map-comp.md) give $\partial x=0$. [Exactness at the quotient](../../l-theory/ultimate/boundary/exact-at-quotient.md) then provides $y$.

## Sources

- HS paper, Section 3

## Depends on

- [Sequence categories](../point-functors/sequence-categories.md)
- [Ultimate L-theory](../../l-theory/ultimate/groups/ultimate-l-group.md)

## Proof depends on

- [Finite-support filtration](../point-functors/finite-support-filtration.md)
- [Boundary then inclusion vanishes](../../l-theory/ultimate/boundary/composite-zero.md), [Ultimate exactness at the quotient](../../l-theory/ultimate/boundary/exact-at-quotient.md), [Coordinates detect $\mathbb L_3(\mathcal S)$](../../l-theory/comparison/coordinates-injective-three.md)
