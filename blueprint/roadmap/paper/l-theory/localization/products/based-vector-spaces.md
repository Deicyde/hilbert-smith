---
article_id: af_e1f03805ebacf59bc9085346
declaration: instance
origin: background
statement: formalized
lean: HSP.FreeQ.instDualCat
---

# Based vector spaces

The duality on the [category of based vector spaces](bookkeeping/based-category.md) $\mathbb Q$ is $(\mathbb Q^d)^*=\mathbb Q^d$ on objects and $g^*=g^{\mathsf T}$ (transpose) on morphisms. It makes $\mathbb Q$ a duality category, and both identities $M^{**}=M$ and $g^{**}=g$ hold on the nose. The standard basis vector $e_i$ of $\mathbb Q^d$ has dual basis vector $e_i^*$, the same vector of $(\mathbb Q^d)^*$.

*Proof sketch.* (Proof obligations.) Transposition reverses products, preserves identities, sums and scalar multiples, and is an involution.

## Sources

- [Ranicki 1992, §1, free modules with the transpose duality](../../../../../sources/paper/ranicki-1992.md) [U]

## Depends on

- [The category of based ℚ-vector spaces](bookkeeping/based-category.md)
- [Duality category](../../base/categories/duality-category.md)
