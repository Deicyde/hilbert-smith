---
article_id: af_026c48406a906c345a6350ca
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.Corner.scalarForget_isStrict
---

# Forgetting to the scalar exterior quotient is strict

Let $n\in\mathbb N$, $R\in\mathbb R$, let $T$ be a compact metric space with a $C_p$-action, possibly empty, and let $\mathbf G$ be a [group sequence](../../categories/asymptotic/group-sequence.md). Then the functor $U^{\mathbf G}:\mathcal B_{\mathbf G,Z}(T\times S^n)\to\mathcal B_{\mathbf 1,Z_0}(S^n)$ [forgetting to the scalar exterior quotient](scalar-forget.md), for the exterior $Z_0$ and $Z=T\times Z_0$, is a strict [duality functor](../../l-theory/base/categories/duality-functor.md): $U^{\mathbf G}(M^*)=U^{\mathbf G}(M)^*$ and its duality isomorphism at $M$ is the identity, for every object $M$. In particular $U'=U^{\mathbf 1}$ and $U$ are strict.

*Proof sketch.* [Forgetting the control space](../../categories/functors/forget-control.md) $U^{\mathbf G}_{\rm c}$ for $X=S^n$, the [round sphere](../round-sphere.md), [is strict](../../categories/functors/forget-control-strict.md), and it carries $\mathcal A_{T\times Z_0}$ into $\mathcal A_{Z_0}$ ([forgetting the control space preserves support](../../categories/functors/forget-control-support.md)). The [induced functor on exterior quotients](../../categories/supports/exterior-functor.md) of a strict duality functor is strict, and $U^{\mathbf G}$ is that induced functor.

## Sources

- HS paper, Sections 10 and 12 (forgetting $T$ and the group).

## Depends on

- [Forgetting to the scalar exterior quotient](scalar-forget.md)
- [Duality functor](../../l-theory/base/categories/duality-functor.md)
- [Group sequence](../../categories/asymptotic/group-sequence.md)

## Proof depends on

- [Induced functor on exterior quotients](../../categories/supports/exterior-functor.md)
- [Forgetting the control space](../../categories/functors/forget-control.md)
- [Forgetting the control space is strict](../../categories/functors/forget-control-strict.md)
- [The round sphere](../round-sphere.md)
- [Forgetting the control space preserves support](../../categories/functors/forget-control-support.md)
