---
article_id: af_3c8fbf4b7108e0d970e67bc4
declaration: def
origin: background
statement: formalized
lean: HSP.karEmb
---

# Embedding into the idempotent completion

For a duality category $\mathcal A$, the *Karoubi embedding* $\mathrm{emb}_{\mathcal A}:\mathcal A\to\mathrm{Kar}\,\mathcal A$ is the functor $M\mapsto(M,1)$, $f\mapsto f$, into the [idempotent completion](karoubi-duality.md). It is a [duality functor](duality-functor.md) whose duality isomorphism at $M$ is the identity of $(M^*,1)=(M,1)^*$; it is [strict](duality-functors/karoubi-embedding-strict.md).

*Proof sketch.* A morphism $f:M\to N$ satisfies $1\circ f\circ1=f$, so it is a morphism $(M,1)\to(N,1)$; identities and composition are those of $\mathcal A$, and the functor is $\mathbb Q$-linear. Since $1^*=1$, $(M,1)^*=(M^*,1)=\mathrm{emb}_{\mathcal A}(M^*)$ and $\mathrm{emb}_{\mathcal A}(f^*)=f^*$, so the identity is a natural duality isomorphism.

**Remark (not formalized).** $\mathrm{emb}_{\mathcal A}$ is fully faithful: a morphism $(M,1)\to(N,1)$ is any $f:M\to N$.

## Sources

- [Ranicki 1992, §1](../../../../../sources/paper/ranicki-1992.md) [U]

## Depends on

- [Idempotent completion with duality](karoubi-duality.md)
- [Duality functor](duality-functor.md)
