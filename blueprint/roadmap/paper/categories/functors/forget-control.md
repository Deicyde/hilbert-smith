---
article_id: af_9ea0cae73ff6d9241d5c7b3a
declaration: def
origin: bridged
statement: formalized
lean: HSP.forgetControl
---

# Forgetting the control space

Let $\mathbf G$ be a [group sequence](../asymptotic/group-sequence.md) and $\mathbf 1$ the [trivial group sequence](../asymptotic/trivial-group-sequence.md). Let $T$ be a compact metric space with an isometric $C_p$-action and $X$ a compact metric space with the trivial $C_p$-action. Give $T\times X$ the maximum metric and the $C_p$-action on the first factor, and let $\mathrm{pr}:T\times X\to X$ be the projection, which is equivariant, continuous and $1$-Lipschitz. Forgetting the control space is the [duality functor](../../l-theory/base/categories/duality-functor.md) between [asymptotic categories](../asymptotic/asymptotic-category.md)
$$U_{\rm c}=U\circ\mathrm{pr}_*:\mathcal A_{\mathbf G}(T\times X)\to\mathcal A_{\mathbf G}(X)\to\mathcal A_{\mathbf 1}(X),$$
the composite of the [pushforward](pushforward.md) along $\mathrm{pr}$ followed by [forgetting the group](forget-group.md). On objects, $(n_i,x_i)$ goes to $(|G_i|\,n_i,\ \mathrm{pr}\circ x_i\circ\mathrm{pr}_2\circ(e^{G_i}_{n_i})^{-1})$, so the generator $e^{G_i}_{n_i}(g,k)$ carries the label $\mathrm{pr}(x_i(k))$, with $e^{G_i}_{n_i}$ the [group enumeration](group-enumeration.md); on morphisms, $[u]\mapsto[\bar u]$, the matrices reindexed along the same enumerations.

The functor itself needs neither that the action on $T$ is isometric nor that the action on $X$ is trivial, because $\mathrm{pr}$ is equivariant for the product action in any case; the triviality is used for the description of the objects, where it gives the labels $\mathrm{pr}(x_i(k))$.

## Sources

- HS paper, Sections 10 and 12 (forgetting $T$ and the group)

## Depends on

- [Group sequence](../asymptotic/group-sequence.md)
- [The trivial group sequence](../asymptotic/trivial-group-sequence.md)
- [Asymptotic category](../asymptotic/asymptotic-category.md)
- [Duality functor](../../l-theory/base/categories/duality-functor.md)
- [Duality on the asymptotic category](../asymptotic/asymptotic-duality.md)
- [The asymptotic category has finite biproducts](../asymptotic/structure/biproducts.md)

## Proof depends on

- [Pushforward of labels](pushforward.md)
- [Forgetting the group](forget-group.md)
- [Identity and composite duality functors](../../l-theory/base/categories/duality-functors/composite-duality-functor.md)
