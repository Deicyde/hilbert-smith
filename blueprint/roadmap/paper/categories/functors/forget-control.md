---
article_id: af_9ea0cae73ff6d9241d5c7b3a
declaration: def
origin: bridged
---

# Forgetting the control space

Let $T$ be a compact metric space with an isometric $C_p$-action and $X$ a compact metric space with the trivial $C_p$-action. Give $T\times X$ the maximum metric and the $C_p$-action on the first factor, and let $\mathrm{pr}:T\times X\to X$ be the projection, which is equivariant, continuous and $1$-Lipschitz. Forgetting the control space is the strict duality functor
$$U_{\rm c}=U\circ\mathrm{pr}_*:\mathcal A_{\mathbf G}(T\times X)\to\mathcal A_{\mathbf G}(X)\to\mathcal A_{\mathbf 1}(X),$$
the [pushforward](pushforward.md) along $\mathrm{pr}$ followed by [forgetting the group](forget-group.md). On objects, $(n_i,x_i)$ goes to the object with generators $G_i\times\{1..n_i\}$, enumerated in the fixed order of forgetting the group, and labels $(g,k)\mapsto\mathrm{pr}(x_i(k))$; on morphisms, $[u]\mapsto[u]$.

## Sources

- HS paper, Sections 10 and 12 (forgetting $T$ and the group)

## Depends on

- [Pushforward of labels](pushforward.md)
- [Forgetting the group](forget-group.md)
