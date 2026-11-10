---
article_id: af_9a19747843cffb43c5b29bbb
declaration: def
origin: bridged
---

# The forgetful functor on tails

Let $\mathbf G=(G_i,\chi_i)$ be a [group sequence](../../categories/asymptotic/group-sequence.md) and $\mathbf 1$ the trivial one. $\bar U:\mathcal V_{\mathbf G}\to\mathcal V_{\mathbf 1}$ is the strict duality functor between the [point categories](../../categories/asymptotic/point-quotient.md) that sends $(n_i)$ to $(|G_i|n_i)$ and $q(u_i)$ to $q(U_{G_i}u_i)$, with $U_{G_i}$ [forgetting the group](forget-functor.md) in coordinate $i$, which reindexes along the group enumeration $e^{G_i}$ of [forgetting the group on the asymptotic category](../../categories/functors/forget-group.md). Then $\bar U\circ q=q\circ U$, where $U=(U_{G_i})_i:\mathcal P_{\mathbf G}\to\mathcal P_{\mathbf 1}$ is the product functor on the [sequence categories](../../categories/asymptotic/point-sequence-category.md), and $\pi_i\circ U=U_{G_i}\circ\pi_i$ hold strictly.

*Proof sketch.* (Well-definedness.) If $u_i=u'_i$ for all but finitely many $i$, then $U_{G_i}u_i=U_{G_i}u'_i$ for the same $i$; by the [point ideal](../../categories/asymptotic/point-ideal.md) the classes agree. Composition, identities and transposes are preserved because each $U_{G_i}$ preserves them.

## Sources

- HS paper, Section 3

## Depends on

- [Group sequence](../../categories/asymptotic/group-sequence.md)
- [Forgetting the group](forget-functor.md)
- [Forgetting the group on the asymptotic category](../../categories/functors/forget-group.md)
- [Point category](../../categories/asymptotic/point-quotient.md)
- [Sequence category](../../categories/asymptotic/point-sequence-category.md)

## Proof depends on

- [Point ideal](../../categories/asymptotic/point-ideal.md)
