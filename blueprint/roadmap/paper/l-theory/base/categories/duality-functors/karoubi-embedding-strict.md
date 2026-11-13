---
article_id: af_b1ac23ebbea1b380f36e5dd0
declaration: lemma
origin: background
statement: formalized
lean: HSP.karEmb_isStrict
proof: formalized
---

# The Karoubi embedding is strict

For a [duality category](../duality-category.md) $\mathcal A$, the [Karoubi embedding](../karoubi-embedding.md) $\mathrm{emb}_{\mathcal A}:\mathcal A\to\mathrm{Kar}\,\mathcal A$ is a [strict](strict-duality-functor.md) duality functor.

*Proof sketch.* For an object $M$, $1_M^*=1_{M^*}$, so $\mathrm{emb}_{\mathcal A}(M^*)=(M^*,1)=(M^*,1^*)=(M,1)^*=(\mathrm{emb}_{\mathcal A}M)^*$, and the duality isomorphism of $\mathrm{emb}_{\mathcal A}$ at $M$ is the identity of this object by definition.

## Sources

- [Ranicki 1992, §1](../../../../../../sources/paper/ranicki-1992.md) [U]

## Depends on

- [Embedding into the idempotent completion](../karoubi-embedding.md)
- [Strict duality functor](strict-duality-functor.md)
- [Small Q-linear category with strict duality](../duality-category.md)
- [Idempotent completion with duality](../karoubi-duality.md)

## Proof depends on

- [Duality functor](../duality-functor.md)
