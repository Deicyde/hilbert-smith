---
article_id: af_724c7265bdabd12dbcc4505e
declaration: def
origin: bridged
statement: formalized
lean: HSP.push
---

# Pushforward of labels

For an equivariant continuous map $f:X\to X'$ of compact metric isometric $C_p$-spaces, $f_*:\mathcal A_{\mathbf G}(X)\to\mathcal A_{\mathbf G}(X')$ is the duality functor $(n_i,x_i)\mapsto(n_i,f\circ x_i)$, $[u]\mapsto[u]$. It is well defined because equivariance gives the labels $f\circ\lambda_i$, and $f$ is uniformly continuous since $X$ is compact, so $\operatorname{prop}(u_i)\to0$ implies the same for the new labels.

The functor needs neither that the actions are isometric nor that $X'$ is compact.

## Sources

- HS paper, Section 2

## Depends on

- [Asymptotic duality](../asymptotic/asymptotic-duality.md)
- [Duality functor](../../l-theory/base/categories/duality-functor.md)
- [Asymptotic category](../asymptotic/asymptotic-category.md)
- [Group sequence](../asymptotic/group-sequence.md)
- [The asymptotic category has finite biproducts](../asymptotic/structure/biproducts.md)

## Proof depends on

- [Free category of a finite group](../asymptotic/free-category.md)
- [Propagation](../asymptotic/propagation.md)
- [Every morphism is a class](../asymptotic/structure/class-surjective.md)
- [Morphisms have propagation tending to zero](../asymptotic/structure/morphism-propagation.md)
- [Small Q-linear category with strict duality](../../l-theory/base/categories/duality-category.md)
