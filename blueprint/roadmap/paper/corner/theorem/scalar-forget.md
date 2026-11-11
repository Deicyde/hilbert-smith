---
article_id: af_d7c5987e30884314e329a4f7
declaration: def
origin: bridged
---

# Forgetting to the scalar exterior quotient

Let $n\ge1$ and $R>0$, let $T$ be a compact metric space with an isometric $C_p$-action, possibly empty, and let $\mathbf G$ be a [group sequence](../../categories/asymptotic/group-sequence.md). Take the [exterior](../exterior.md) $Z_0\subseteq S^n$ of the [round sphere](../round-sphere.md) and $Z=T\times Z_0$. Let $U^{\mathbf G}_{\rm c}:\mathcal A_{\mathbf G}(T\times S^n)\to\mathcal A_{\mathbf 1}(S^n)$ be [forgetting the control space](../../categories/functors/forget-control.md) for $X=S^n$. It carries $\mathcal A_{T\times Z_0}$ into $\mathcal A_{Z_0}$ ([forgetting the control space preserves support](../../categories/functors/forget-control-support.md), with $Z_0$ closed by [the exterior is closed](../exterior-closed.md)), so it induces the [functor on exterior quotients](../../categories/supports/exterior-functor.md)
$$U^{\mathbf G}:\mathcal B_{\mathbf G,Z}(T\times S^n)\to\mathcal B_{\mathbf 1,Z_0}(S^n),\qquad M\mapsto U^{\mathbf G}_{\rm c}M,\quad[u]\mapsto[U^{\mathbf G}_{\rm c}u],$$
a strict duality functor. We write $U'=U^{\mathbf 1}:\mathcal B_{\mathbf 1,Z}(T\times S^n)\to\mathcal B_{\mathbf 1,Z_0}(S^n)$ for the trivial group sequence, and $U=U^{\mathbf G}$ when $\mathbf G$ is the group sequence of the standing data.

## Sources

- HS paper, Sections 10 and 12 (forgetting $T$ and the group).

## Depends on

- [The exterior](../exterior.md)
- [The round sphere](../round-sphere.md)
- [The exterior is closed](../exterior-closed.md)
- [Group sequence](../../categories/asymptotic/group-sequence.md)
- [Forgetting the control space](../../categories/functors/forget-control.md)
- [Forgetting the control space preserves support](../../categories/functors/forget-control-support.md)
- [Induced functor on exterior quotients](../../categories/supports/exterior-functor.md)
