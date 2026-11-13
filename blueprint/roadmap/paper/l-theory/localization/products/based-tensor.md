---
article_id: af_4af78b87b5f4af640ec254d1
declaration: def
origin: background
statement: formalized
lean: HSP.basedTensorPairing
---

# Tensor product of based vector spaces

On the duality category $\mathbb Q$ of [based vector spaces](based-vector-spaces.md), put $\mathbb Q^a\boxtimes\mathbb Q^b=\mathbb Q^{ab}$, with $e_i\boxtimes e_j=e_{(i-1)b+j}$ for $1\le i\le a$, $1\le j\le b$, and let $f\boxtimes g$ be the [Kronecker product](bookkeeping/based-kron.md) of the matrices $f$ and $g$, whose entry in row $(i-1)b'+j$ and column $(k-1)b+l$ is $f_{ik}g_{jl}$. With $\kappa$ the identity, $(\boxtimes,\mathrm{id})$ is a [duality pairing](duality-pairing.md) $\mathbb Q\times\mathbb Q\to\mathbb Q$.

*Proof sketch.* (Proof obligations.) $(f'f)\boxtimes(g'g)=(f'\boxtimes g')(f\boxtimes g)$ is the mixed-product rule for Kronecker products, identities go to identities, and $\boxtimes$ is bilinear entrywise. $(\mathbb Q^a\boxtimes\mathbb Q^b)^*=\mathbb Q^{ab}=(\mathbb Q^a)^*\boxtimes(\mathbb Q^b)^*$, and $(f\boxtimes g)^{\mathsf T}=f^{\mathsf T}\boxtimes g^{\mathsf T}$, so the identity is natural, and its dual is the identity.

## Sources

- New: the Kronecker product, for the chain models of the chain-model chapter.

## Depends on

- [Based vector spaces](based-vector-spaces.md)
- [Duality pairings](duality-pairing.md)
- [The category of based ℚ-vector spaces](bookkeeping/based-category.md)

## Proof depends on

- [Small Q-linear category with strict duality](../../base/categories/duality-category.md)
- [Kronecker product of matrices](bookkeeping/based-kron.md)
