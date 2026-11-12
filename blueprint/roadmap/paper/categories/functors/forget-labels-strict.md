---
article_id: af_3ec47827b970c41f5e0889f0
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.forgetLabels_isStrict
---

# Forgetting labels is strict

Let $\mathbf G$ be a [group sequence](../asymptotic/group-sequence.md) and $X$ a metric space with a $C_p$-action. Then [forgetting labels](forget-labels.md) $\Phi:\mathcal A_{\mathbf G}(X)\to\mathcal V_{\mathbf G}$ is a strict [duality functor](../../l-theory/base/categories/duality-functor.md): $\Phi(M^*)=\Phi(M)^*$ and its duality isomorphism at $M$ is the identity, for every object $M$.

*Proof sketch.* The dual of $(n_i,x_i)$ has the same ranks $n_i$, and the dual of $(n_i)$ in $\mathcal V_{\mathbf G}$ is $(n_i)$, so $\Phi(M^*)=\Phi(M)^*$. The duality isomorphism of $\Phi$ is the identity by definition.

## Sources

- HS paper, Section 3

## Depends on

- [Forgetting labels](forget-labels.md)
- [Duality functor](../../l-theory/base/categories/duality-functor.md)
- [Group sequence](../asymptotic/group-sequence.md)
