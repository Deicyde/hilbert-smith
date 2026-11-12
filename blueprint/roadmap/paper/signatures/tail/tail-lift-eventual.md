---
article_id: af_d0044cb1882e69bc18508fb4
declaration: theorem
origin: bridged
statement: formalized
lean: HSP.tail_lift_eventually
---

# Lifts agree eventually

Let $\mathbf G$ be a [group sequence](../../categories/asymptotic/group-sequence.md), with [sequence category](../../categories/asymptotic/point-sequence-category.md) $\mathcal P_{\mathbf G}$, [coordinate functors](../../categories/asymptotic/point-coordinate-projection.md) $\pi_i:\mathcal P_{\mathbf G}\to\mathrm{Free}(\mathbb Q[G_i])$ and [quotient functor](../../categories/asymptotic/point-quotient-functor.md) $q:\mathcal P_{\mathbf G}\to\mathcal V_{\mathbf G}$ onto the [point category](../../categories/asymptotic/point-quotient.md). If $y,y'\in\mathbb L_4(\mathcal P_{\mathbf G})$ and $q_*y=q_*y'$, then $(\pi_i)_*y=(\pi_i)_*y'$ in $\mathbb L_4(\mathrm{Free}(\mathbb Q[G_i]))$ for all but finitely many $i$.

This rests on the open statements [Lemma U](../../l-theory/comparison/lemma-u.md), through [classes in $\mathbb L_4(\mathcal S)$ have finite support](../../l-theory/comparison/coordinates-finite-four.md), and [lifting](../../l-theory/localization/boundary/lift-to-pair.md), through [ultimate exactness in the middle](../../l-theory/ultimate/boundary/exact-in-middle.md).

*Proof sketch.* $q_*(y-y')=0$, so $y-y'=i_*z$ with $z\in\mathbb L_4(\mathcal S_{\mathbf G})$ by [ultimate exactness in the middle](../../l-theory/ultimate/boundary/exact-in-middle.md), applied to the [point filtration](../../categories/asymptotic/point-filtration.md) with inclusion $i$. Since $\pi_i\circ i$ is the coordinate functor of $\mathcal S_{\mathbf G}$, [functoriality](../../l-theory/ultimate/groups/induced-map-comp.md) gives $(\pi_i)_*(y-y')=(\pi_i)_*z$, which vanishes for all but finitely many $i$ by [the finite-support theorem](../../l-theory/comparison/coordinates-finite-four.md).

## Sources

- HS paper, Section 3

## Depends on

- [Group sequence](../../categories/asymptotic/group-sequence.md)
- [Sequence category](../../categories/asymptotic/point-sequence-category.md)
- [Point category](../../categories/asymptotic/point-quotient.md)
- [Free category of a finite group](../../categories/asymptotic/free-category.md)
- [Induced map on ultimate L](../../l-theory/ultimate/groups/induced-map.md)
- [Coordinate projection of the sequence category](../../categories/asymptotic/point-coordinate-projection.md)
- [The quotient functor of the point category](../../categories/asymptotic/point-quotient-functor.md)

## Proof depends on

- [Point filtration](../../categories/asymptotic/point-filtration.md)
- [Ultimate exactness in the middle](../../l-theory/ultimate/boundary/exact-in-middle.md)
- [Functoriality on ultimate L](../../l-theory/ultimate/groups/induced-map-comp.md)
- [Classes in $\mathbb L_4(\mathcal S)$ have finite support](../../l-theory/comparison/coordinates-finite-four.md)
