---
article_id: af_3c8fbf4b7108e0d970e67bc4
declaration: def
origin: background
---

# Embedding into the idempotent completion

For a duality category $\mathcal A$, the *Karoubi embedding* $\mathrm{emb}_{\mathcal A}:\mathcal A\to\mathrm{Kar}\,\mathcal A$ is the functor $M\mapsto(M,1)$, $f\mapsto f$, into the [idempotent completion](karoubi-duality.md). It is a strict [duality functor](duality-functor.md).

*Proof sketch.* A morphism $f:M\to N$ satisfies $1\circ f\circ1=f$, so it is a morphism $(M,1)\to(N,1)$; identities and composition are those of $\mathcal A$, and the functor is $\mathbb Q$-linear. Since $1^*=1$, $(M,1)^*=(M^*,1)=\mathrm{emb}_{\mathcal A}(M^*)$ and $\mathrm{emb}_{\mathcal A}(f^*)=f^*$, so the identity is a duality isomorphism and the functor is strict.

**Remark (not formalized).** $\mathrm{emb}_{\mathcal A}$ is fully faithful: a morphism $(M,1)\to(N,1)$ is any $f:M\to N$.

## Sources

- [Ranicki 1992, §1](../../../../../sources/paper/ranicki-1992.md) [U]

## Depends on

- [Idempotent completion with duality](karoubi-duality.md)
- [Duality functor](duality-functor.md)
