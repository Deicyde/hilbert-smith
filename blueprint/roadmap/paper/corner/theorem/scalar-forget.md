---
article_id: af_d7c5987e30884314e329a4f7
declaration: def
origin: bridged
statement: formalized
lean: HSP.Corner.scalarForget
---

# Forgetting to the scalar exterior quotient

Let $n\ge1$ and $R>0$, let $T$ be a compact metric space with an isometric $C_p$-action, possibly empty, and let $\mathbf G$ be a [group sequence](../../categories/asymptotic/group-sequence.md). Take the [exterior](../exterior.md) $Z_0\subseteq S^n$ of the [round sphere](../round-sphere.md) and $Z=T\times Z_0$, and the [exterior quotients](../../categories/supports/exterior-quotient.md) $\mathcal B_{\mathbf G,Z}(T\times S^n)$ and $\mathcal B_{\mathbf 1,Z_0}(S^n)$, with $\mathbf 1$ the [trivial group sequence](../../categories/asymptotic/trivial-group-sequence.md). Let $U^{\mathbf G}_{\rm c}:\mathcal A_{\mathbf G}(T\times S^n)\to\mathcal A_{\mathbf 1}(S^n)$ be [forgetting the control space](../../categories/functors/forget-control.md) for $X=S^n$. It is a [strict](../../categories/functors/forget-control-strict.md) duality functor, and it carries $\mathcal A_{T\times Z_0}$ into $\mathcal A_{Z_0}$ ([forgetting the control space preserves support](../../categories/functors/forget-control-support.md)). So it induces the [functor on exterior quotients](../../categories/supports/exterior-functor.md), whose construction takes a strict duality functor,
$$U^{\mathbf G}:\mathcal B_{\mathbf G,Z}(T\times S^n)\to\mathcal B_{\mathbf 1,Z_0}(S^n),\qquad M\mapsto U^{\mathbf G}_{\rm c}M,\quad[u]\mapsto[U^{\mathbf G}_{\rm c}u],$$
a [duality functor](../../l-theory/base/categories/duality-functor.md) with duality isomorphism the class of that of $U^{\mathbf G}_{\rm c}$. We write $U'=U^{\mathbf 1}:\mathcal B_{\mathbf 1,Z}(T\times S^n)\to\mathcal B_{\mathbf 1,Z_0}(S^n)$ for the trivial group sequence, and $U=U^{\mathbf G}$ when $\mathbf G$ is the group sequence of the standing data.

The construction needs neither $n\ge1$, $R>0$, the isometry of the action on $T$, nor the closedness of $Z_0$.

## Sources

- HS paper, Sections 10 and 12 (forgetting $T$ and the group).

## Depends on

- [The exterior](../exterior.md)
- [The round sphere](../round-sphere.md)
- [Group sequence](../../categories/asymptotic/group-sequence.md)
- [The trivial group sequence](../../categories/asymptotic/trivial-group-sequence.md)
- [Exterior quotient](../../categories/supports/exterior-quotient.md)
- [Duality functor](../../l-theory/base/categories/duality-functor.md)

## Proof depends on

- [Forgetting the control space](../../categories/functors/forget-control.md)
- [Forgetting the control space is strict](../../categories/functors/forget-control-strict.md)
- [Forgetting the control space preserves support](../../categories/functors/forget-control-support.md)
- [Induced functor on exterior quotients](../../categories/supports/exterior-functor.md)
- [Support subcategory](../../categories/supports/support-subcategory.md)
- [Asymptotic category](../../categories/asymptotic/asymptotic-category.md)
- [Quotient by a subcategory](../../l-theory/base/categories/filtration-quotient.md)
