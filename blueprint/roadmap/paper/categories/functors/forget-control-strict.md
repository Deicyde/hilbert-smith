---
article_id: af_53f0811ec87abc176d7d94e8
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.forgetControl_isStrict
---

# Forgetting the control space is strict

Let $\mathbf G$ be a [group sequence](../asymptotic/group-sequence.md), and let $T$ and $X$ be compact metric spaces with $C_p$-actions. Then [forgetting the control space](forget-control.md) $U_{\rm c}:\mathcal A_{\mathbf G}(T\times X)\to\mathcal A_{\mathbf 1}(X)$ is a strict [duality functor](../../l-theory/base/categories/duality-functor.md): $U_{\rm c}(M^*)=U_{\rm c}(M)^*$ and its duality isomorphism at $M$ is the identity, for every object $M$.

*Proof sketch.* $U_{\rm c}=U\circ\mathrm{pr}_*$ is the composite of the [pushforward](pushforward.md) along the projection and [forgetting the group](forget-group.md). Both have identity duality isomorphisms and commute with the dualities on objects, so, by the formula for the duality isomorphism of a composite, so does $U_{\rm c}$.

## Sources

- HS paper, Sections 10 and 12 (forgetting $T$ and the group).

## Depends on

- [Forgetting the control space](forget-control.md)
- [Duality functor](../../l-theory/base/categories/duality-functor.md)
- [Group sequence](../asymptotic/group-sequence.md)

## Proof depends on

- [Pushforward of labels](pushforward.md)
- [Forgetting the group](forget-group.md)
