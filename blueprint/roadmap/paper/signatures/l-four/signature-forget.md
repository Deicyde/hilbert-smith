---
article_id: af_e43fe2b3c812c2f42a7608d7
declaration: lemma
origin: bridged
---

# Forgetting keeps the integer signature

For $x\in L^p_4(\mathrm{Free}(\mathbb Q[G]))$, $\sigma_1((U_G)_*x)=\sigma_G(x)$, where $U_G$ is [forgetting the group](../point-functors/forget-functor.md).

*Proof sketch.* Choose a representative $x=[C,\varphi]$, so $(U_G)_*x=[U_GC,(U_G)_\%\varphi]$ ([induced map](../../l-theory/base/groups/induced-map.md)). $U_G$ reindexes every matrix along the fixed enumeration of $G\times\{1..n_r\}$. The permutation matrix of this reindexing is orthogonal and carries the real cochains, the coboundary and $\varphi_2$ of $U_GC$ to those of $C$, so it induces an isometric isomorphism from $b_{U_GC}$ to $b_C$, the latter with the $G$-action forgotten. Conclude with [isometry invariance](../forms/form-signature-isometry.md) for the trivial group and [the identity value](../forms/form-signature-identity.md).

## Sources

- HS paper, Section 3

## Depends on

- [Forgetting the group](../point-functors/forget-functor.md)
- [Integer signature](integer-signature.md)
- [Induced homomorphism](../../l-theory/base/groups/induced-map.md)

## Proof depends on

- [Isometry invariance](../forms/form-signature-isometry.md)
- [Value at the identity](../forms/form-signature-identity.md)
